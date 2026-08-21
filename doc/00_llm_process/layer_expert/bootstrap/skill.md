# bootstrap Layer Expert

## Role

Own layer-specific process knowledge for the 4-stage bootstrap pipeline (see
`doc/07_guide/compiler/build.md` § "Bootstrap Stages" for the authoritative
definition — this doc used to undercount it as "3-stage"):
`src/compiler/80.driver/driver_bootstrap.spl` orchestrates seed (Rust) → stage2
(Simple on Rust, `bootstrap_main.spl` entry) → stage3 (self-hosted Simple
binary — Stage-2's output recompiles itself, still the minimal
`bootstrap_main.spl` entry, NOT the full CLI) → stage4 (the verified Stage-3
binary compiles `main.spl`, producing the actual deployable full-CLI
`bin/simple` with every subcommand). "Self-hosted" (Stage 3) and "full CLI
usable" (Stage 4) are distinct milestones — a Stage-3-only binary answers
`compile`/`native-build` but has no `run`/`test`/`duplicate-check`, by design.
This layer also owns the JIT Cranelift backend stability track (stage2 uses
LLVM llc by default; JIT is opt-in via `SIMPLE_BOOTSTRAP_REAL_LLVM` env var).
Tracks redeploy gate (`scripts/check/cert/redeploy_gate/redeploy_gate.shs`), smoke-matrix
verification, and all bootstrap-blocking regressions.

## Pipeline Links

## SimpleOS 32-bit cross-target boundary

The shared consumer contract is
`src/os/port/simpleos_32bit_bootstrap_contract.spl`. It keeps host Phase 1/2
lineage distinct from guest execution and permanently refuses to reinterpret
cross-built QEMU evidence as target-native compiler execution. Do not close
Todo 834-836 from source tests, a Rust seed, or synthetic serial markers.

- [verify skill](../../../../.claude/skills/verify.md)
- [impl skill](../../../../.claude/skills/impl.md)

## Layer Links

- Driver: [src/compiler/80.driver/driver_bootstrap.spl](../../../../src/compiler/80.driver/driver_bootstrap.spl)
- Gate: [redeploy_gate.shs](../../../../scripts/check/cert/redeploy_gate/redeploy_gate.shs)
  (smoke-matrix fixture verification before any forward push).
- Bootstrap stages plan:
  [doc/03_plan/compiler/bootstrap/redeploy_stage4_plan_2026-07-09.md](../../../../doc/03_plan/compiler/bootstrap/redeploy_stage4_plan_2026-07-09.md).
- Rust seed: `src/compiler_rust/compiler/src/pipeline/` (stage2 compiler only;
  after stage3 hand-off, seed not executed by default).
- Unit specs: `test/01_unit/compiler/80.driver/` (e.g. `driver_bootstrap_spec.spl`).

## Cranelift Bootstrap Path & LLVM Redeploy Status (2026-07-18)

### Stage-scoped development admission

Focused pure-Simple compiler/interpreter/loader work may use an explicitly
admitted Stage 2 or Stage 3 binary according to
`doc/07_guide/compiler/minimal_bootstrap_configuration_composition.md`. Record
its absolute path, hash, stage, provenance, and supported commands; isolate
output/cache and fail closed. Such evidence proves only the named stage and
command. It is not Stage 4, general SPipe/docgen/test, release, convergence,
DDC, or cross-host evidence, and it must never hide a Rust-seed fallback.

**Cranelift Path Working:** `sh scripts/bootstrap/bootstrap-from-scratch.sh --backend=cranelift` completes stages 2–3 reliably. Full-CLI requires `--full-bootstrap` to avoid driver stale-backfill rejection. See [doc/07_guide/compiler/build.md § Cranelift Bootstrap Path](../../../../doc/07_guide/compiler/build.md).

**LLVM Path Blocked:** Stage 2 link has 62 residual undefined symbols (method lowering gap). See [doc/08_tracking/bug/seed_stage2_llvm_method_symbol_lowering_2026-07-17.md](../../../../doc/08_tracking/bug/seed_stage2_llvm_method_symbol_lowering_2026-07-17.md).

**Stage-4 Caveat:** Hours-long spins observed when stage-3 was built by pre-fix seed. Root: InterpCall handicap in Cranelift (symbol lowering delay). See [doc/08_tracking/bug/s68_cranelift_interpcall_boxed_result_generic_return_gap_2026-07-18.md](../../../../doc/08_tracking/bug/s68_cranelift_interpcall_boxed_result_generic_return_gap_2026-07-18.md).

## WP-3.5 — lint-oracle staleness probe (2026-08-07)

`bin/simple lint` runs `bin/release/x86_64-unknown-linux-gnu/simple`, which is
proven to be a **Rust seed** build (prints the seed WARNING banner), not a
self-hosted binary. It contains `MEXH001` (present in
`src/compiler_rust/compiler/src/lint/types.rs`) but not `MEXH006` or
`W-MC-RES-001` (pure-Simple-only diagnostics in `src/compiler/90.tools/lint`
and `src/compiler/35.semantics/lint`) — those can never appear in a seed
binary regardless of how it's rebuilt; they require a genuine Stage-3
self-host.

Staleness probe: `scripts/check/check-lint-binary-staleness.shs` (grep-only,
no build; `--selftest` proves the PASS branch without a real redeploy).
Process doc:
[doc/07_guide/compiler/lint_binary_redeploy_process.md](../../../../doc/07_guide/compiler/lint_binary_redeploy_process.md).

The historical lane chose T3 because the changed source was under
`src/compiler`; that path-based rule is obsolete. Current work must use
[minimal-bootstrap feature development](../../../07_guide/compiler/minimal_bootstrap_configuration_composition.md)
and escalate only from compatibility evidence or an explicit release/trust
target. The attempted full
`--full-bootstrap --deploy` run reached Stage 3 and SIGSEGV'd during
`phase=monomorphize` / MIR lowering (exit 139, ~394s wall, 10.7 GB peak RSS,
no diagnostic). See
[doc/08_tracking/bug/t3_full_bootstrap_stage3_unresolved_type_byteorder_cache_validator_2026-08-06.md](../../../../doc/08_tracking/bug/t3_full_bootstrap_stage3_unresolved_type_byteorder_cache_validator_2026-08-06.md).
This blocks every Wave-2 WP's ability to observe its own lint-based fix
through the deployed binary, not just WP-3.5.

## Redeploy #79 Status (2026-07-10)

**Wall:** short-circuit `and`/`or` undef dominance (#135, not yet fixed).

**Fixed (landed):**
- **RuntimeDict never grew — THE stage-4 in-process wall (2026-07-11):** compiled-code
  dicts were fixed-capacity (slots inline, `rt_dict_set` → `false` on full, bool
  ignored by compiled code) so the 9th insert into any `{}` silently dropped —
  `SymbolTable.scopes` lost scope 9+ → nil-receiver trap = deployed binary's instant
  `native-build` crash, `check` exit-3, and the reason test/check still delegate.
  Fix: [src/compiler_rust/runtime/src/value/dict.rs](../../../../src/compiler_rust/runtime/src/value/dict.rs)
  (separate slot alloc + ×2 growth at 3/4 load). Reaches `bin/simple` only after
  seed/runtime rebuild + stage-4 redeploy. Companion fix: Cranelift adapter mapped
  `Host` → x86-64 (Linux ELF objects on arm64 macs);
  [cranelift_codegen_adapter.spl](../../../../src/compiler/70.backend/backend/cranelift_codegen_adapter.spl)
  now resolves via `host_arch()`. Debug chain:
  [stage4_compiled_dict_no_growth_2026-07-11.md](../../../../doc/08_tracking/bug/stage4_compiled_dict_no_growth_2026-07-11.md).
- **#131 dup-SSA phi allocation** (var_reassign_ssa.spl): alloca slot reuse
  across distinct SSA values caused phi duplication under Cranelift. Fix:
  [src/compiler/60.mir_opt/mir_opt/var_reassign_ssa.spl](../../../../src/compiler/60.mir_opt/mir_opt/var_reassign_ssa.spl)
  (verify alloca freshness per SSA root).
- **#133 nil-arg-types guarded** (core_codegen.spl): LLVM type-check now guards
  all nil call arguments with `valid_llvm_type()` before marshalling to Cranelift.
  [src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl](../../../../src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl).

**2026-07-11 evening follow-up (redeploy #79 root-cause & perf hardening):**
- **check hang wall:** check worker spawned as the `bin/simple` SYMLINK → argv0-based
  seed-sibling lookup in `_cli_driver_binary()` fails → no delegation → in-process frontend
  grind on full check app + compiler imports → parser gap #2 at mailbox.spl:525 → 300s kill.
  Fix: `resolve_worker_binary()` in
  [src/app/cli/check_entry.spl](../../../../src/app/cli/check_entry.spl) (spawn real
  `bin/release/<triple>/simple`; 300s+ → 2.9s). Debug: [stage4_compiled_dict_no_growth_2026-07-11.md](../../../../doc/08_tracking/bug/stage4_compiled_dict_no_growth_2026-07-11.md) § evening follow-up.
- **print-loss wall ROOT-CAUSED:** seed's bootstrap-MIR/LLVM lane lowers `[text].join(sep)`
  to a SILENT NULL constant (no runtime call emitted, no error) — CLI print builtin joins its
  args, so all in-process prints die; `rt_print_str` (core_string.spl) silently no-ops on the
  degenerate (0x1,0) pair → exit-0 loss. Literals/concat fine; interpolation `"{n}"` prints
  literal braces in the same lane ([bootstrap_mir_interpolation_literal_braces_2026-07-11.md](../../../../doc/08_tracking/bug/bootstrap_mir_interpolation_literal_braces_2026-07-11.md)). Fix pattern = commit `b48d79b8c6`
  (route method through rt_* runtime call).
- **self-hosted parser gaps:** dedent-continuation CLOSED (lexer rule G27,
  [self_hosted_parser_dedent_continuation_2026-07-11.md](../../../../doc/08_tracking/bug/self_hosted_parser_dedent_continuation_2026-07-11.md));
  block-lambda-as-call-arg OPEN ([mailbox.spl:525](../../../../src/app/interpreter/async_runtime/mailbox.spl#L525)).
- **parser hot-path getenv hoist:** per-token `rt_env_get` calls in `par_line_set`/`par_col_set`
  cached to lazy process-lifetime flag (`par_env_save_enabled()`); 5 sites in
  [src/compiler/10.frontend/core/parser.spl](../../../../src/compiler/10.frontend/core/parser.spl).

**Prior fixes (redeploy #79 init):**
- **#128 HIR block tail-drop** (HirBlock.has): expressions weren't recognizing
  tail-drops in single-expr blocks.
- **#130 arg-wipe in seed stage2**: bootstrap_main arg handling.

## Redeploy #79 Operator Notes (2026-07-11)

**Parse-Error Gate False-Positives:** The phase-2 parse-error gate
(`par_had_error` check) is structurally correct but false-positives on
speculative/fragment re-lex errors. Bootstrap gate may spuriously fail during
stage2 diagnosis. Workaround: diff the actual Hir output to confirm semantic
correctness; known bug, fix in flight.

**Driver Import Pattern:** `use lazy` dynload for the compiler driver was
never implemented. `bootstrap_main.spl` now imports `compiler.driver.driver`
directly. Any driver initialization changes must verify this direct import
path still resolves.

**Native-Build Closure Discovery Limitation:** The recursive closure tracer
follows plain `use` imports but does NOT traverse `export use` shims. Only
direct imports trigger cascading collection. If re-exporting driver or
lowering modules, closure must be assembled manually or closure-tracer
extended to handle shims.

**Runtime Library Path:** `SIMPLE_RUNTIME_PATH` env var MUST be set to the
seed target directory for hosted native-build linking. The `--runtime-path`
CLI flag alone does not set the env var. Host-side wrappers must explicitly
pass both: `SIMPLE_RUNTIME_PATH="path/to/seed/target" bin/simple native-build`.
Hosted link will backfill `rt_*` externs from `libsimple_native_all.a` only if
the env var points to the correct seed target.

## Gotchas

1. **JIT path is opt-in:** seed stage2 defaults to LLVM llc (via
   `SIMPLE_BOOTSTRAP=1` without `SIMPLE_BOOTSTRAP_REAL_LLVM`). Cranelift gate
   tests are manual. Do not force JIT as default without smoke-matrix sign-off.
2. **Redeploy gate enforces smoke matrix:** any forward push must pass
   `scripts/check/cert/redeploy_gate/redeploy_gate.shs` (compiler lint/fmt/check + bootstrap
   stage2/stage3 round-trip + test subset). Gate failures are hard stops.
3. **stage2 binary is ephemeral:** only used during bootstrap. After stage3
   succeeds, discard it — no production reliance on stage2 artifacts.
4. **Deployed `simple` is a frontend; SSpec needs its `simple_seed` sibling.**
   The release CLI delegates `test` to a `simple_seed` in the SAME directory
   (`seed sibling not found, skipping delegation` = it's missing → in-process
   fallback fails `unresolved name: describe`). Every deploy must ship the
   pair. Recovery: copy a known-good `{simple, simple_seed}` pair from a clean
   worktree's `build/bootstrap/full/<triple>/` to a scratch dir.
   See `cli_symlink_argv0_seed_sibling_lookup_2026-07-24.md`.
   **Exe identity must be resolved IN-PROCESS.** `_cli_current_exe_path` now
   canonicalizes `/proc/self/exe` via `rt_path_absolute`
   (`std::fs::canonicalize`). Never shell out for it: a `/proc/self` read done
   by a spawned helper describes the HELPER, so `readlink -f /proc/self/exe`
   returned `/usr/bin/readlink` — its seed sibling `/usr/bin/simple_seed` never
   exists, so the CLI fell through to delegate to `bin/simple` = itself and
   `bin/simple run` became an unbounded fork bomb (2026-07-25, `0531ca8ce266`).
   The same commit restored `_cli_resolve_symlink` on the *candidate* side of
   `_cli_is_current_exe`: `bin/simple` is a symlink, so an unresolved candidate
   never matches our real exe and the fork-bomb guard silently passes.
   **Binaries deployed before `0531ca8ce266` self-delegate no matter which path
   invokes them** — identity does not depend on argv[0] in those builds, so the
   old "invoke the REAL path, not the symlink" workaround does not help. Drive
   `simple_seed` directly until redeploy.
5. **Stale untracked `.smf` stubs poison module resolution tree-wide** —
   symptom is identical to a deploy clobber (every spec fails
   `unresolved name: describe`). `find src test -name '*.smf'` must be empty;
   quarantine hits. See
   `doc/08_tracking/bug/smf_stub_shadowing_unresolved_describe_2026-07-24.md`
   and `doc/07_guide/infra/testing.md` § Troubleshooting.

## Multi-Error Recovery Strategy

Bootstrap recovery has two explicit modes. Use **fail-fast** for normal
CI/release gates or a hard blocker that prevents later diagnostics. Use
**inventory-to-end** when failures appear one at a time, many bugs are likely,
or the task asks for the broadest possible error inventory.

In inventory-to-end mode, freeze the source/compiler/runtime identities and a
deterministic task manifest, then run the whole requested scope with isolated
per-task processes, cache directories, and timeouts. Continue after errors and
persist total/completed/failed/remaining counts plus logs. Do not begin edits
until the manifest reaches its end. If per-file startup makes that impractical,
retain the resumable manifest and switch to coarser module/root tasks that still
cover the complete scope; never repeatedly restart from item zero.

The preferred runner is `scripts/check/compiled-check-tree.py` with a compiled
`src/app/check/main.spl`, bounded batches, and durable `manifest.tsv`, `run.json`,
batch, and isolated-file results. Use `--resume` only when the checker and
manifest identities match. The legacy shell diagnostic sweep is for short
probes; its temporary terminal rows are not resumable inventory evidence.

After the sweep, normalize the first real diagnostic, collapse cascades and
duplicates, and claim each unique category in the bug database. Assign one
root-cause category per agent, not one symptom or file per agent. Agents use
separate caches and must not edit the same compiler/runtime owner. Fix all
affected instances through the smallest shared owner, add an exact reproducer
and similar-situation tests, rerun only failed shards, then run one authoritative
main build. A diagnostic seed/check pass is not Stage-4 authority: every result
must name the executable, mode, target, host, and manifest.

Convergence requires the scoped inventory to be complete, every category fixed
or explicitly recorded as blocked/platform-unavailable, failed shards green,
and the requested CLI plus sanity gates green. Apply the repository's three-cycle
cap and do not rerun already-green criteria.

## Session update 2026-07-18

**Release-mode interpreter stack-overflow guard now default-ON:** interpreter 
detects stack exhaust and returns an error instead of crashing, improving 
robustness in production builds.

**fs_helpers file_exists self-shadow recursion fixed:** file_exists no longer 
calls itself recursively, resolving stack issues in filesystem operations.

**NEW OPEN BUG — implicit-self field assignment (doc/08_tracking/bug/interp_implicit_self_field_assignment_silent_noop_2026-07-17.md):** 
in `me` methods, field assignments without explicit `self.` prefix silently 
no-op, while the lint recommends the implicit form. This is a semantic error 
that needs investigation.

**Canonical redeploy path:** `scripts/bootstrap/bootstrap-from-scratch.sh --backend=cranelift` 
(LLVM feature absent in cargo seed; Cranelift is the canonical JIT target for self-hosted stage3).
See `doc/03_plan/compiler/bootstrap/redeploy_stage4_plan_2026-07-09.md` for blocker tracking.

**f-string interpolation contract (fix 2026-07-17):** unescaped `"` inside `{...}` 
toggles nested string literal; unmatched `{` containment via newline guard for non-triple f-strings 
(parser/src/lexer/strings.rs, regression ca58e1f reverted).

**Stage-3 blocker FIXED 2026-08-01 — `true_*`/`false_*` call args (doc/08_tracking/bug/parser_true_false_prefix_call_arg_2026-08-01.md):**
`parse_call_arg_raw` read any call argument whose identifier started with `true_`
or `false_` as a *suffixed bool literal*, the rest of the name being a type
suffix. The Rust seed has no such production. Loud mode: `f(true_target.id)` and
`f(true_count + 1)` fail to parse (this is what killed Stage 3 on
`vulkan_backend.spl:1109`). Silent mode: `f(true_value)` parses but becomes
`true` with type suffix `value` → `unresolved type: value`, a likely contributor
to the 3,350 `unresolved type` errors previously blamed entirely on match-arm
scoping. Production removed, not narrowed — narrowing leaves the silent path.

**Gotcha — reproduce stage-3 parse failures WITHOUT a 21-minute bootstrap.** The
stage2 binary from any prior run (`build/bootstrap/stage2/<triple>/simple`) is a
standalone compiler; drive it with `native-build` on a scratch `.spl`. The bug
above went from "whole-tree parse-state defect, unreproducible in isolation" to a
9-line standalone repro this way.

**Gotcha — `bin/simple` is NOT the Rust seed.** It reports `simple-bootstrap
1.0.0-beta` and carries pure-Simple frontend bugs. The real seed oracle is
`src/compiler_rust/target/bootstrap/simple` (prints a "bootstrap seed only"
warning banner). Use it, not `bin/simple`, when asking "what is the correct
behaviour?" during bootstrap work.

## 2026-08-06 Stage 3 blocker family — several fixed, one still OPEN

### Cached render carrier handoff (2026-08-14)

Follow `doc/07_guide/ui/rendering/cached_render_entry_closure.md`. A purported
non-seed artifact under `release/` returns `missing command` for direct source
execution and exit 0/no output for native-build, while current source owns
fail-closed output checks. This is a blocker and possible stale/miscompiled
dispatcher, not proof of root cause or deployed Stage 4 lineage. Require exact
candidate, essential-smoke, provenance, deploy, and rollback receipts before
the render carrier build. Bug:
`doc/08_tracking/bug/self_hosted_cli_native_build_silent_no_artifact_2026-08-14.md`.

A dense sequence of Stage-3 self-host blockers were root-caused and fixed this
session (chronological, each superseding the previous hypothesis where noted):

- Non-termination (not a crash): `find_reexport_source` needed memoization
  (`548f2d3b1f6`, writeup `80eeb22ee7f`).
- Stack overflow: removed a `SymbolTable` scope guard that recursed unboundedly
  (`030ff43e330`) — **this fix is what re-opened the ud2 crash below**, see
  that entry for the current unresolved state.
- Dead `Effect`/`EffectSet` re-exports broke Stage 3 self-host (`35c8086a06b`).
- Missing `ByteOrder` import + an `Effect` facade collision (`9bb8727cbc3`) —
  **this is the currently-cited KNOWN BLOCKER for `bin/simple` provenance**
  (`t3_full_bootstrap_stage3_unresolved_type_byteorder_cache_validator_2026-08-06.md`).
  Do not re-open or contradict this status; it is genuine and still tracked.
- SIGSEGV: an untyped local made a vtable-bearing class read fields at the
  wrong offset — this was a field-offset RELRO write bug, not a MIR-lowering
  crash as first suspected (`9078535133c` → fixed `92d059e5ce7`).
- LLVM triple corruption: a one-slot field-offset shift, not an "empty arch"
  as first suspected (`dc8186a0e71`; the seed-mechanism hypothesis in an
  earlier doc was explicitly retracted, `057a15f09c7`).
- C runtime objects were dropped from the Stage 3 link line; put back
  (`52be0cdbc23`, corrected record `e1c7e10fafe`).
- `try_lower_bitfield_construct` SIGSEGV from a stale scope-chain lookup —
  guarded (`1ea6599e8fb`, in `switch_operators_calls.spl`).
- Generic native-build SIGSEGV confirmed to be seed-vs-selfhosted-scoped, not
  uname/target-detection-specific (`1d17d3cc657`).

**Still OPEN as of this session's last check:** `SymbolTable.lookup` ud2
nil-receiver crash. First diagnosed `789639d54f7`, then **the root cause was
corrected** — it's a binary-provenance mismatch (comparing a disassembled
binary that was NOT built from this repo's WC), not a codegen bug
(`e099de44b8f`). After correcting the WC to match `origin/main`, the
underlying scope-tracking bug is confirmed real and still open: fixing it with
an `rt_dict_contains` guard causes a *worse* failure (stack overflow, the same
bug `030ff43e330` fixed by removing a guard) — so neither "guard" nor
"no guard" is currently correct. Full detail and next-step options:
`doc/08_tracking/bug/stage3_symboltable_lookup_ud2_field_access_nil_receiver_2026-08-06.md`.
**Do not assume this is fixed** — check that doc's status before building on
top of Stage 3 self-host claims.

## Downstream feature experts depending on this layer (2026-08-06)

- [feature_expert/simpleos_toolchain_selfhost](../../feature_expert/simpleos_toolchain_selfhost/skill.md)
  — the SimpleOS clang+Simple migration. It depends on **exactly the seed-vs-
  self-hosted distinction this layer owns**: because the deployed self-hosted
  `bin/release/simple` SEGVs on `native-build` (**D1**,
  `deployed_selfhost_env_set_miscompile_segv_2026-07-14.md`), its
  `bin/release/x86_64-unknown-simpleos/simple` payload was built by
  `src/compiler_rust/target/bootstrap/simple` as a route-around. That makes the
  payload **staging evidence, never self-hosted evidence** — a redeploy landing
  here is what upgrades it. Related layer:
  [llvm_toolchain_port](../llvm_toolchain_port/skill.md).

## 2026-08-08 Stage 2 restored; Stage 3 monomorphize SIGSEGV still open

**Stage 2 was down, now fixed (`e7df6e01`):** an incomplete
`Mailbox`→`PriorityMailbox` rename (`a019ba19aa6`) left two defects: it
resurrected a dead `__init__.spl` "Re-exported from mailbox.spl" block that a
prior commit (`983058c5ff39`) had deleted, and left
`actor_scheduler.spl` with 3 stale `Mailbox` references (import, field type,
constructor call) to a type that no longer existed. Stage 2 died with `llvm
global load referenced undeclared symbol 'Mailbox'`. Fixed by renaming the 3
references and dropping the resurrected re-export block (verified: fresh
worktree, `build_stage2.sh` → exit 0, 794 compiled, 0 failed, linked ELF
125109 KB). Trap for future renames: **the frontend does not reject
undeclared field/type references at the point of use** — this class of defect
only surfaces downstream as an HIR-consumer/LLVM-global error, not a
parse/type error at the rename site. See
`doc/08_tracking/bug/stage2_mailbox_priorimailbox_rename_incomplete_blocks_build_2026-08-08.md`
and `doc/08_tracking/bug/actor_scheduler_mailbox_new_unresolvable_after_rename_2026-08-08.md`.

**Stage 3 `phase=monomorphize` SIGSEGV on `method=len` is a separate, still-OPEN
blocker** (diagnosis in flight as of this writing; no dedicated bug doc filed
yet under `doc/08_tracking/bug/` — do not assume one exists, and do not
conflate this with the WP-3.5 byteorder/cache-validator blocker documented
above, which is a different crash signature at the same phase). Anyone
resuming Stage 3 self-host work should re-check for a doc under
`stage3_monomorphize` or `method_len` naming before starting a fresh
diagnosis, since the fix may have landed since this note was written.

## Lint cost + binary provenance, measured 2026-08-09

Confirms and quantifies the WP-3.5 staleness note above. `bin/simple` →
`bin/release/x86_64-unknown-linux-gnu/simple` **is a Rust seed**; probe it
positively, since size and banner both lie:

```bash
bin/simple --version 2>&1 | head -2
# WARNING: this Rust-built Simple binary is a bootstrap seed only; ...
```

The staged pure-Simple binaries `bootstrap/stage{1,2,3}/simple` (3.4 MB,
identical) expose only `compile` and `native-build` — `stage3 lint` is
`unknown command`, exit 1 (fails closed). So **no pure-Simple binary can lint
today**, and `simple test` GREEN cannot prove anything self-hosted.

**The symlink target changes under you.** Three distinct release binaries in
one session: 29,573,408 B (Aug 8 12:14) → 58,940,120 B (Aug 9 04:30) →
29,577,536 B (Aug 9 04:50). Fixed lint startup moved 11.70s → 42.97s across
one of those swaps. Record `stat -c '%s %y' "$(readlink -f bin/simple)"` with
every timing, or the number is not reproducible.

**Lint cost model** (the circulating "4.4s/run" is stale; RSS ~350 MB still
matches): `≈ 11.7s startup + ~3.3–4.0s per function declaration`, superlinear
in declaration count (~n^1.25), driven by declaration count not bytes. A
120-line file costs ~119s. **Batching is worse** (2 files >600s vs 119s for
1). Phase split via `lint` vs `fmt --check` vs a 24-byte file: startup 10%,
parse 20%, **lint rules 70%**.

Fast path: `sh scripts/check/lint-cached.shs <files>` — 152.00s cold → 0.03s
warm, clean verdicts only. Note it invalidates on every rebuild, so in a busy
shared WC the payoff window is minutes. Full numbers, safety proofs, and
profiler dead ends (perf paranoid=4; gdb ptrace_scope=1 returns zero stacks
while exiting 0): `doc/07_guide/tooling/build_fast_path.md`.

## Update Rule

After any bootstrap, JIT stability, or redeploy-gate change, refresh this skill
with new wall status, fixed issue links, and concrete gotchas.

Template: `.spipe/spipe/doc/00_llm_process/template/layer_skill.md`

## Phase snapshots + resource policy (2026-08-17)

**Phase-snapshot convention** — `build/phase_snapshots/README.md`. Immutable,
lineage-named per-phase binaries: `phase1_<t1>/`, `phase1_<t1>_phase2_<t2>/`,
`..._phase3_<t3>/`, each holding `simple` (+ `.a` if needed). A snapshot is
copied ONCE at phase completion and never overwritten; phase N+1 (and every
side-lane task) runs against an explicit snapshot path — never `bin/simple`,
never the in-place stage output, both of which get replaced mid-flight. A
mid-bootstrap fix landing = a NEW generation (new t1); in-flight phase2/3
tasks keep their old lineage until done. The bootstrap script has its own
sibling mechanism: `src/compiler_rust/target/bootstrap.generations`
(`scripts/bootstrap/bootstrap-from-scratch.sh:1067`).

**Resource policy during bootstrap** — the phase compiler build OWNS
CPU/memory. Test/tool lanes run beside it `nice`d, capped at <=2 concurrent
test processes. earlyoom kills `simple` first under pressure: a 3.1 GB test
worker was killed at 9.97% free memory this session — an OOM-killed lane looks
like a crash, so check `dmesg`/earlyoom logs before debugging the binary.

**Parallel find-and-fix fleet** — sweep per-DIRECTORY under `timeout`,
dropping to per-FILE on a crash, so one crashing file never stops the sweep.
Land fixes in the SOURCE tree: later stages compile them in for free. Land via
scoped plumbing commits (only your paths) through all 7 pre-push guards
(`.claude/rules/vcs.md`). Fixes cross-linked from this round: seed sqlite
emulation (`208f11786f8`: DELETE WHERE fail-closed, real BEGIN/ROLLBACK
snapshots, UNIQUE), argv publish for delegated subcommands (`bdafd9d5b5a`,
`rt_set_args_vec`), `rt_file_atomic_write` in the Rust staticlib
(`src/compiler_rust/native_all/src/lib.rs:1155`).

## Snapshot-tree bootstrap gotchas (2026-08-17, later same day)

- **A frozen rsync tree must include vendored `gen/` dirs AND a `.git`.** A
  blanket `--exclude 'gen/'` stripped `src/compiler_rust/vendor/typenum/src/gen`
  and broke offline cargo (vendored checksums no longer match). And the stage
  engine binds Stage-3 identity to git HEAD/dirty state, so a snapshot tree
  without `.git` fails there too. Snapshot = full tree minus build outputs only.
- **planner-admission-v2 gate is unconditionally fail-closed** — it currently
  blocks ALL bootstraps; see
  `doc/08_tracking/bug/bootstrap_admission_v2_fail_closed_blocks_all_bootstraps_2026-08-17.md`.
  Last known-working script version: `b1ff6537ed8` ("feat: add admitted Stage4
  resume checkpoint").
- **Incremental profile clamps `selfhost_jobs` to 2**
  (`scripts/bootstrap/bootstrap-from-scratch.sh:815-819`). On a big box patch
  to 16 (fallback 8 when free memory < 40 GB) — the clamp is tuned for small
  machines.
- **Phase-generation rule:** if two phase-1 generations land before phase 2
  starts, phase 2 uses the NEWEST. Phases never stop at the first failure when
  forward progress is possible — collect ALL problems through phase 4, then
  fix in one pass.

**Standing test rule:** every bug fix ships (1) a spec reproducing the exact
defect and (2) a generalization spec probing similar problems nearby, both
cited in the bug doc. A fix without its reproducing spec is not done.

## Build-lane doctrine + pipeline bugs (2026-08-17, third round)

- **Exactly ONE compile-build owner at a time.** Two concurrent stage-2 builds
  nearly triggered earlyoom. Deconfliction: the SCRIPT-DRIVEN run survives;
  any ad-hoc/manual build yields and waits or pins to a snapshot.
- **Phase builds never wait for verification.** Sanity/tool-harness checks
  always run in a parallel `nice`d lane beside the phase build, never inline.
- **Phase 2 completed via dynload** — the phase-4 relink therefore needs
  `--full-cli` / `--mode=one-binary`; a dynload-shaped phase-2 output is not
  the one-binary artifact.
- **Pipeline bugs observed this session** (no bug docs filed yet — file on
  next touch): (1) stage-2 exits 1 SILENTLY with a 0-byte log under the
  transcribed sandbox env; (2) a phantom `stage2-capability.log` reference in
  the pipeline; (3) native-build has no keep-going flag — first error aborts
  the whole build, forcing the per-directory/per-file sweep workaround above.
- **Canonical phase-2-found compiler bug:** the LintDiag LLVM codegen defect —
  a real miscompile surfaced only by building the compiler with the phase
  binary. Treat phase 2 as a compiler-bug detector, not just a build step.
- **Stale-base clobber pattern (3 incidents tonight):** an agent editing on a
  stale base and landing verbatim reverts other sessions' fixes. Rules:
  commit SCOPED immediately after editing (Edit-tool changes are not
  auto-snapshotted), and the push lane must graft PER-FILE diffs onto current
  origin — never land a whole file verbatim. See `.claude/rules/vcs.md`
  (anti-revert protocol) for the general form.
## Per-phase run-to-end loop (2026-08-17)

Doctrine for every bootstrap generation, per phase:

1. **Run the phase to the end.** Never stop at the first error where the
   tooling can keep going — collect a FULL error census for the phase. One
   error per run is the slowest possible way to learn what is broken.
2. **Snapshot the phase binary immutably** the moment it lands, with lineage
   naming (phase + generation + source sha), so later timing/verification
   claims name an artifact that cannot be swapped underneath them. The
   symlink `bin/simple` is replaced by other sessions mid-session — a
   snapshot is the only stable referent.
3. **Verify completely, in a parallel niced lane**: attempt ALL tool builds
   even when some fail (another full census, not a first-failure abort), plus
   the test suites run with that exact snapshot.
4. **Start the next phase on the NEWEST available binary.** If a rebuild is
   in flight, wait for it rather than starting on a stale one.
5. Repeat the whole cycle per generation.

**Memory priority.** The phase compiler build owns CPU and memory; test lanes
throttle to 1 concurrent process when free RAM is low. Measured 2026-08-17
(session-measured, unfiled): earlyoom killed `jobs=8` stage workers while ~14
test lanes ran, forcing the build down to `jobs=2`. Verification lanes are
subordinate to the build, never co-equal.

**Silent-green hazard (HIGH).** `bin/simple test <spec>` has been measured
emitting ~1897 warning lines, ZERO pass/fail lines, and exit 0 —
`doc/08_tracking/bug/test_runner_emits_no_result_summary_silent_exit0_2026-08-17.md`.
Never accept exit 0 as proof of pass in a phase verification lane: require an
explicit results/count line, otherwise mark the lane INCONCLUSIVE and confirm
with a direct `bin/simple run` repro.

## Per-lane private build caches (2026-08-17)

Concurrent bootstrap lanes (phase-1 seed, phase-2 stage, phase-3 self-host,
phase-4 full CLI, census, tool builds) may run DIFFERENT compiler binaries over
the SAME source tree. Both engines' native-build cache scope keys now carry a
**lane** axis on top of the compiler identity they already had:
`SIMPLE_CACHE_SCOPE=<name>`, or `--cache-scope <name>` on the Rust
native-build / native-all CLIs. Unset ⇒ `default` (previous behaviour).

Entries are partitioned by a scope-derived DIRECTORY, so a cross-scope lookup
cannot name an out-of-scope entry — the miss is structural, not a hash compare.
Each cache dir records its owner in a `.cache_scope` marker; check ownership
without running a compiler via `scripts/check/check-cache-scope-ownership.shs
<cache-dir> <lane>` (PASS/FAIL/ERROR, `--selftest`). `bootstrap-from-scratch.sh`
gives each stage `build/bootstrap/native_cache/<lane>/` and refuses fail-closed
to build against another lane's cache; `resume-stage3-from-admitted.sh` fences
its stage2/stage3 dirs the same way.

- Design: `doc/05_design/compiler/incremental_build/per_lane_private_caches.md`
- Rust: `src/compiler_rust/compiler/src/pipeline/native_project/mod.rs`
  (`cache_lane`, `cache_scope_segment`, `cache_dir`, `object_cache_key`)
- Pure Simple: `src/compiler/80.driver/driver_build/incremental.spl`
  (`native_build_cache_lane`, `native_build_cache_scope_key`)
- Specs: `test/01_unit/compiler/cache/per_lane_cache_scope{,_prevention}_spec.spl`
- NOT changed: dependency-aware partial rebuild (`interface_digest_of`,
  `simple.sdn` traversal, `SmfManifest` load-verification remain uncalled).

---

## 2026-08-21 — snapshot pinning, PARTIAL fail-closed, threads

**What landed** (`src/compiler_rust/driver/src/cli/commands/misc_commands.rs`):
- Bootstrap input **snapshot pinning** — stages read a pinned snapshot instead of the live
  working tree (`bootstrap/.input-snapshot/`), so a parallel session's edit can no longer race
  a determinism comparison.
- `PARTIAL` outcomes are now **fail-closed** — a partial stage result is an error, not a pass.
- Threaded stage execution.
- Seed fixes shipped alongside: builtin-name shadowing, interpreter unwrap, vulkan externs,
  owned-process runtime restore.

**Gates:**
- `sh scripts/check/check-seed-builds-push.shs` → `PASS — <n> file(s) checked, seed bin + test
  targets compile cleanly at <sha> (seed content <digest> recorded green; ...)`.
- `sh scripts/check/check-c-runtime-compiles-push.shs` → after the owned-process runtime restore:
  `FAIL — 1 file(s) failed to compile: src/runtime/test/rt_browser_renderer_namespace_selfcheck.c
  (107 compiled clean, 2 skipped ...)` (was `FAIL — 5 file(s) failed to compile ... (103 compiled clean)`).
- `sh scripts/check/check-stage-binaries-runnable.shs` → still ADVISORY/RED: all four tracked
  stage binaries SEGV on `compile` and `native-build`.

**Bugs filed 2026-08-21:**
- `doc/08_tracking/bug/bootstrap_determinism_check_races_live_working_tree_2026-08-21.md` (the reason for snapshot pinning)
- `doc/08_tracking/bug/owned_process_runtime_lost_in_tree_wipe_restore_2026-08-21.md`
- `doc/08_tracking/bug/module_fn_shadowed_by_builtin_name_2026-08-21.md` — `Results: 4 total, 4 passed, 0 failed`
- `doc/08_tracking/bug/seed_helper_return_type_mistyped_as_tuple_2026-08-21.md`
- Still open and blocking self-host parity: `stage3_native_build_and_compile_segv_on_hello_world_2026-08-18.md`

**Depending feature expert:** `feature_expert/compiler_hardening/skill.md` (Phase 7 parity).
