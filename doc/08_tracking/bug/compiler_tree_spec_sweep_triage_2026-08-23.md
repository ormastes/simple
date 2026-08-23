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
