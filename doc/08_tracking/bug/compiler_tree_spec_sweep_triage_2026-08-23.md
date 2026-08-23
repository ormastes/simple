# Compiler-tree spec sweep triage — `test/01_unit/compiler/**`, 2026-08-23

11 non-green specs under `test/01_unit/compiler/**` were reproduced
INDIVIDUALLY with `bin/simple test <path>` (the sweep's
`Process exited with code 1` loses which example failed). Binary used:
the Rust seed at `bin/release/x86_64-unknown-linux-gnu/simple`, size
60536008, copied from the deployed tree; it self-identifies as a bootstrap
seed. **Engine for every row below is the INTERPRETER** unless stated —
JIT and native resolve independently and none of these were re-checked
there.

## Resolved in this pass

| spec | verdict | before -> after |
|---|---|---|
| `compiler/ffi_gen/backend_gating_spec.spl` | SPEC-WRONG (stale `ffi_gen` -> `sffi_gen` rename) | 1 total/0 passed -> 2 total/2 passed |
| `compiler/mir_opt/auto_vectorize_spec.spl` | SPEC-WRONG (`LoopInfo` -> `VectorLoopInfo`) | 5 failures -> 64 total/64 passed |
| `compiler/irdsl/parser_validator_spec.spl` | **SOURCE-WRONG** (two bugs) | 1 total/0 passed -> 1 total/1 passed |

`compiler/bootstrap/ast_native_arena_spec.spl` was partially repaired: the
`SIMPLE_NATIVE_ARENA_DECLS` source-text assertion was retargeted (the source
legitimately moved from a literal `0` default to
`ast_decl_arena_default()`, `_Ast/decl_nodes.spl:169,177`). Not committed —
the same example still fails on a second, unrelated tripwire, see below.

## Handed to owning lanes — NOT edited from here

### `src/compiler/50.mir/**` (MIR construct-matrix lane)

`compiler/mir_opt/cipher/cipher_intrinsics_spec.spl`, 3/3 failures.
`is_cipher_intrinsic` returns false for EVERY registered cipher intrinsic.
Full record with the interpreter repro and the 12-site defect-class sweep:
`doc/08_tracking/bug/is_cipher_intrinsic_always_false_dotq_on_i64_optional_2026-08-23.md`.

### `src/compiler/20.hir/**` (HIR construct-matrix lane)

`compiler/hir/alias_static_call_resolution_spec.spl`, 2/2 failures, both
`assert_true failed: got false`. This spec's own header states both
assertions **PASSED** when it was written (2026-07-17) and that it is "a
preventing test, not a reproduction of a live bug". Both are now RED, so
alias resolution through `use {Real as Alias}` for static-method-call and
constructor callees has **regressed** — the exact ALIAS-GAP class fixed in
the seed at `3f0acf071cf`. Suspect surface named by the spec's own
`@cover` lines: `20.hir/hir_lowering/_Items/module_lowering.spl`
(`register_imported_symbol` / `rename_symbol`) and
`20.hir/hir_lowering/expressions.spl` (`symbol_display_name` baking the
canonical name into `HirExprKind.NamedVar`). Treat as a regression, not a
new gap.

#### Cross-reference: very likely the SAME construct as `runtime_file_rename`

Routed here after the coordinator flagged three failed fix attempts on
`runtime_file_rename`. Checked, and the connection is real but needs stating
precisely, because it is **not** literally one code path:

`src/lib/nogc_sync_mut/io/file_ops.spl:218-220` is

```
use std.io_runtime.{file_rename as runtime_file_rename}

fn file_rename(src: text, dst: text) -> bool:
    runtime_file_rename(src, dst)
```

That is `use {Real as Alias}` with the alias used in **callee position** — the
exact construct, and the exact position, that
`compiler/hir/alias_static_call_resolution_spec.spl` guards.

The two are separate IMPLEMENTATIONS of the same resolution step:

| | `runtime_file_rename` | this red spec |
|---|---|---|
| tree | Rust seed, `src/compiler_rust/**` | pure-Simple, `src/compiler/20.hir/**` |
| site | `hir/lower/lowerer.rs::collect_flattened_import_aliases` | `hir_lowering/_Items/module_lowering.spl` (`register_imported_symbol` / `rename_symbol`) |
| failure | alias left unresolved -> `Linkage::Import` named after the ALIAS | callee resolves to something other than the alias TARGET |

So: **same construct, same defect class, two implementations** — not
provably one root cause, and a fix to either proves nothing about the other.

What makes this worth escalating rather than filing as a coincidence: the
pure-Simple spec's own header asserts that this architecture is *structurally
immune* to the seed's failure — "pure-Simple resolves the alias ONCE, at import
registration ... so there is only one source of truth for every consumer",
explicitly contrasted with "the Rust seed's per-consumer ad-hoc name
reconstruction". Both assertions are now red, so that immunity claim is
**empirically false today**. The pure-Simple side has either lost the
single-resolution property or grown a consumer that re-derives the name.
Verify which before attempting a fix; the header's architectural claim can no
longer be trusted as a starting assumption.

Concrete candidate shape for the pure-Simple fix, from what worked in the seed:
the seed's root cause was that its two resolution tiers (owner-mangled symbol,
else bare `source_name` if unique) BOTH declined — tier 2 because the flattened
unit held **four** `file_rename` definitions and it refused as ambiguous. The
fix added a third tier keyed on the flattener's own module-owner tag
(`tag_function_module_owner`). If pure-Simple's failure is also an
ambiguity-refusal against several same-named targets, the same owner-tag
disambiguation is the shape to try. Confirm the ambiguity first — do not port
the tier blind.

### `src/compiler/10.frontend/core/**` (contested)

`compiler/bootstrap/ast_native_arena_spec.spl`, 4/5 failures.
1. Source-text tripwire: spec wants `var stmt_env_mirror_slot: [bool]` and
   `return stmt_env_mirror_slot[0]` in `core/ast_stmt.spl`. The stmt side
   now uses scalar module vars (`stmt_env_mirror_cached` / `stmt_mode_ready`,
   `ast_stmt.spl:123-138`) while the **expr** side still uses the `[bool]`
   slot form. That asymmetry looks like an INCOMPLETE refactor rather than a
   stale spec — decide which shape is canonical before touching the spec.
2. `array index out of bounds: index is 0 but length is 0` on sequential
   module resets.
3. Generic return type lost: `fn boxed() -> SiblingBox<i64>` yields `Any`,
   not `SiblingBox`.
4. Interpreter bootstrap env mirrors ignored when the native arena is
   disabled: `expr_get_int` returns 7 (the real value) instead of 88 (the
   env mirror).

### Silent-miscompile lane

- `compiler/codegen/any_typed_value_consumption_class_spec.spl`, 2/5
  failures — "renders an untyped function result as a number" and "has no
  failing check under either engine". A genuine ANY-decode miscompile; the
  spec explicitly compares engines, so this is NOT interpreter-only.
- `compiler/concurrent/concurrent_backend_store_parity_class_spec.spl`, 1/1
  — the **native** backend sub-run emits `SWEEP-FAILED` where the pure-std
  run emits the full value list. Native-only divergence.

### Other, not yet root-caused

- `compiler/extern/rt_file_read_bytes_single_extern_signature_spec.spl`,
  1/7 — "declares exactly one return type repo-wide", expected 3 to equal 1.
  Measured across `src/`: `[u8]` x28 (authoritative), `[u8]?` x8,
  `[i64]?` x2. SOURCE-WRONG; the convergence is real but cannot land from
  this lane because one of the 10 offending declarations is
  `src/compiler_rust/lib/std/src/infra/file_io.spl:83`, owned by the Rust
  seed lane. The `[i64]?` pair
  (`src/lib/nogc_sync_mut/io/telnet_serial_bridge.spl:31`,
  `src/lib/nogc_sync_mut/sfm/container.spl:15`) is the worst of it: a
  4-to-8-fold element-width disagreement against the C runtime ABI.
- `compiler/interpreter/aliased_param_writeback_spec.spl`, 1/4 — the
  example that fails is named "pins the known-open both-aliases-mut
  residual so it cannot move unnoticed", i.e. the spec is a deliberate
  pin on a KNOWN-OPEN residual. Do not "fix" by weakening it.
- `compiler/linker/assurance_object_note_spec.spl`, 1/5 —
  `semantic: type mismatch: cannot convert array to int` in
  `add_assurance_note_section`.

## Pre-existing test-tree divergence at landing time (required record)

`sh scripts/check/check-test-tree-divergence.shs --ref HEAD` verdict on the
tip of this range:

```
5957 pairs compared, 5100 identical, 857 diverged
baseline has 854 known-diverged entries
NEW divergence(s) not in baseline:
  + integration:storage/dbfs/dbfs_no_regression_spec.spl
  + unit:os/kernel/arch/riscv32_boot_spec.spl
  + unit:os/kernel/loader/executable_source_vfs_spec.spl
FAIL — 857 diverged vs 854 baselined (3 new, 0 fixed-but-still-baselined);
1 mirror-only (0 unallowlisted, 0 stale-allowlist)
```

**All three are pre-existing and none is introduced by this range.** Verified
by comparing each pair's blob hashes at BASE (`origin/main`) and at NEW
(this tip) directly with `git cat-file blob` — committed content on both
sides, never the shared working copy:

| pair | at `origin/main` | at this tip |
|---|---|---|
| `dbfs_no_regression_spec.spl` | DIVERGED | DIVERGED |
| `riscv32_boot_spec.spl` | DIVERGED | DIVERGED |
| `executable_source_vfs_spec.spl` | DIVERGED | DIVERGED |

Identical status on both sides, so the offender list is unchanged across the
range. Three independent checks agree:

1. This range touches exactly **four** files under `test/` — the two members
   of `compiler/ffi_gen/backend_gating_spec.spl` and the two of
   `compiler/mir_opt/auto_vectorize_spec.spl` — and nothing else, so no other
   pair can have moved.
2. Both pairs are **byte-identical** between `test/01_unit` and `test/unit` at
   this tip (sha256 `b30573663aa57736` and `7873d8ec2bb2ff7f` respectively),
   so neither introduces divergence.
3. **Neither pair appears in** `scripts/check/test_tree_divergence_baseline.txt`
   (854 rows), so neither can be a stale-baseline flip in the other direction
   either.

### Deviation from the documented escape, stated rather than glossed

`vcs.md` specifies `check-test-tree-divergence-delta.shs <BASE> <NEW>` for this
situation. That helper runs the full guard **twice**. It was attempted three
times on this range and **never produced a verdict**: ~45 min at load 59, then
~140 min at load 46-48, then the single-sided form at ~180 min. Total ~5.5 h of
guard runtime, zero verdicts, while `origin/main` advanced 3 commits in 14
minutes — i.e. the base goes stale roughly ten times faster than the delta
helper can validate a range on this box. The single-sided guard eventually
terminated and is the verdict quoted above; the BASE side was then established
by targeted blob comparison of exactly the three named pairs rather than by a
second full scan. That is narrower than the helper but sound for the question
asked, and it is recorded here so the shortcut is visible rather than implied.

Worth filing separately: a mandatory pre-push guard that cannot finish inside
the repo's own merge cadence is a landing blocker for every lane, not just
this one.
