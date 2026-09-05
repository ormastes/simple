# Stage-3 self-host failure: `unresolved name: error` in backend type-mapper/codegen files

Date: 2026-08-08
Status: FIX LANDED (source), FULL-BOOTSTRAP VERIFICATION IN PROGRESS — root
  cause confirmed by static analysis + a targeted regression spec; the ~30min
  end-to-end `--full-bootstrap --deploy` RED/GREEN proof was still running at
  time of writing (background run had to rebuild the Rust seed first because
  concurrent lanes touched `src/compiler_rust/**` today). Update this line
  with the final PASS/FAIL once that run completes.

## Root cause (confirmed)

`src/lib/common/error.spl` (module `std.error`) and
`src/lib/common/error/error.spl` (module `std.error.error`) each independently
defined an identical `extern class SimpleError` and
`pub fn error(message: text) -> SimpleError`. The second file had **zero
importers anywhere in the tree** (confirmed by grepping for
`use std.error.error` and for its other exports `rt_error_value` /
`rt_method_not_found` — no hits outside the file itself) — pure dead code.

Both `error` definitions nonetheless enter the self-hosted (Stage-3)
compiler's whole-program global function symbol table (the six poisoned
backend files never `use` the `std.error` module directly — `error(...)` is
resolved as a bare/global builtin-style call, not a locally-imported symbol).
The duplicate definition made global resolution of the name `error` fail for
whichever files were processed in the "loses" branch of the duplicate,
producing "unresolved name: error" — matching exactly the 12 real call sites
across the 6 poisoned files (llvm_type_mapper.spl ×2, common/type_mapper.spl
×1, cuda_type_mapper.spl ×1, cuda/ptx_builder.spl ×5, vulkan_type_mapper.spl
×1, lua_backend.spl ×2 — lua_backend.spl's other 3 `error(` occurrences are
inside string literals emitting generated Lua source and are not Simple call
sites). Stage 2 (compiled by the Rust seed) was unaffected because the seed's
builtin/global resolution path differs from the self-hosted resolver's.

This is the same *family* of bug as today's `compiler_cross_module_private_symbol_collision`
warning class ("N co-compiled definitions with differing signatures") — except
`error`'s two definitions had **identical** signatures, so no warning fired,
and instead of falling back to "last definition wins" the self-hosted resolver
appears to drop/invalidate the symbol outright once the collision is
detected, which is consistent with a hard "unresolved name" rather than a
silently-wrong dispatch.

## Fix

Deleted the orphaned duplicate module `src/lib/common/error/error.spl`
(`git rm`). Pure dead-code removal — zero importers, so no caller is affected.
`SimpleError` / `error(...)` remain defined exactly once, in
`src/lib/common/error.spl`.

## Files changed

- `src/lib/common/error/error.spl` — deleted (dead duplicate of `std.error`)
- `test/01_unit/compiler/backend/std_error_no_duplicate_definition_guard_spec.spl`
  — new regression spec (grep/file-existence based): asserts the duplicate
  file stays deleted and the canonical `std.error` module still defines
  `error`/`SimpleError`. **3 examples, 0 failures**, confirmed passing via
  `bin/simple test test/01_unit/compiler/backend/std_error_no_duplicate_definition_guard_spec.spl`.

## Verification status

- Unit-level regression spec: **GREEN** (3/3), see above — this is a
  source-assertion-only guard, not a compile/build proof.
- Full `--full-bootstrap --deploy` RED/GREEN (the only proof that Stage 3
  itself now passes): **started, not yet complete** at time of writing. The
  run had to rebuild the Rust seed first (concurrent lanes modified
  `src/compiler_rust/**` today), adding ~6min before Stage 2/3 even begin, so
  the full ~30min proof was not available within this task's window. This
  status line must be updated with the actual Stage-3 PASS/FAIL (and Stage-4
  reachability) once that run finishes — do not mark this bug CLOSED before
  that.
Area: compiler / backend (`src/compiler/70.backend/backend/`), Stage 3 self-host
  (stage2-compiled `simple` compiling itself via `native-build`)

## Discovery context

Found while verifying the fix for
`stage2_native_build_run_fn_undefined_reference_link_failure_2026-08-08.md`.
That fix is confirmed working: a full `--full-bootstrap --deploy` run now
prints `Stage 2 native-build capability passed` (no more `undefined reference
to 'run_fn'`). The pipeline then proceeds to Stage 3 self-host and fails there
for a **different, unrelated** reason:

```
[collect-all] <value:0x6> module(s) poisoned, 12 error(s) collected across 559 source(s) in phase 3 (HIR lowering).
[collect-all] Poisoned modules are DROPPED; downstream passes do not run. Diagnostics below are ROOT causes, not a cascade.
[collect-all]   poisoned: src/compiler/70.backend/backend/llvm_type_mapper.spl
[collect-all]   poisoned: src/compiler/70.backend/backend/common/type_mapper.spl
[collect-all]   poisoned: src/compiler/70.backend/backend/cuda_type_mapper.spl
[collect-all]   poisoned: src/compiler/70.backend/backend/cuda/ptx_builder.spl
[collect-all]   poisoned: src/compiler/70.backend/backend/vulkan_type_mapper.spl
[collect-all]   poisoned: src/compiler/70.backend/backend/lua_backend.spl
[ERROR] phase 3 FAILED
error: in-process native-build: HIR lowering error in src/compiler/70.backend/backend/llvm_type_mapper.spl: unresolved name: error
... (12 total, same message, across the 6 files above)
warning: stage3 self-host failed (exit 1); Stage 4 unavailable
Stage 2 native-build capability passed
Stage 3 unavailable — no provenance-verified compiler for Stage 4
error: full CLI build requires a verified pure-Simple stage2/stage3 compiler; refusing seed fallback
```

Full log:
`/tmp/claude-1000/-home-ormastes-dev-pub-simple/df59455b-ebc5-4a4b-b4af-aae8c10e43c0/scratchpad/bootstrap_out/logs/x86_64-unknown-linux-gnu/stage3-native-build.log`
(scratchpad path, not preserved beyond this session — re-run to reproduce).

## Likely site

Each poisoned file calls a bare `error(...)` as what looks like a builtin
panic/raise function, e.g.
`src/compiler/70.backend/backend/llvm_type_mapper.spl:178` and `:277`:

```
error("Unsupported type in LLVM backend: {ty}")
error("Cannot compute size of {ty}")
```

`unresolved name: error` during HIR lowering suggests the Stage-3 self-hosted
compiler's HIR lowering pass does not resolve `error` as a builtin/global
function in this context — either a builtin-registration gap specific to the
stage2-compiled (native-build) compiler, or a name-resolution regression that
doesn't affect Stage 2 (which is itself compiled by the Rust seed, not by a
pure-Simple compiler) but does affect Stage 3 (pure-Simple compiling
pure-Simple). Not yet established whether `error` is a genuine stdlib/builtin
function missing from the self-hosted resolver's builtin table, or a
different kind of shadowing/scope bug. All 6 poisoned files are backend
type-mapper/codegen modules — worth checking whether they share an import or
pattern the other 553 non-poisoned Stage-3 sources don't.

## Repro

```
sh scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --deploy --output=<path outside repo tree> --progress
```

Same repro as the `run_fn` bug; this failure surfaces after Stage 2 now
succeeds. Full run takes ~15-30 min with the Rust seed already built.

## Next steps

- Grep for `error(` as a bare call (not `Err(`/`.error(`) across
  `src/compiler/70.backend/backend/` and compare against the builtin table the
  Stage-3 (self-hosted) HIR lowering resolver consults, vs. whatever the
  Rust-seed-compiled Stage-2 resolver consults for the same call.
- Check `git log -p` / `git blame` on `error(` call sites and the builtin
  registration for `error` for a recent rename/gap.
- Root-cause and fix in `.spl` source only, per project rules; verify Stage 3
  completes and Stage 4 becomes reachable.
