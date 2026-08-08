# Stage-3 self-host: `Symbol` struct/type_alias conflict and nil-receiver crash

Status: OPEN
Date: 2026-08-04
Lane: stage-3 self-host blocker sweep

## What was fixed (closed here)

`driver_dict_entry_count` was the last *generic-function* blocker:

```
error: in-process native-build: generic functions are not supported on the native
build path yet: fn 'driver_dict_entry_count' declares type parameter(s);
monomorphization is not implemented (#158 Phase B)
[driver/driver_hir_pipeline_lowering.spl]
```

It was de-genericised to its single production instantiation
(`Dict<SymbolId, HirFunction>`) in `6fd61352ae7`. **Monomorphization was NOT
implemented.** The Phase A hard stop in
`src/compiler/20.hir/hir_lowering/_Items/declaration_lowering.spl` (functions,
classes, structs) is intact and #158 Phase B remains open.

### Generic-function census of the Stage-3 closure

16 generic `fn` declarations exist under `src/compiler/**`, but the Stage-3
closure only ever reaches **4** of them:

| function | file | status |
|---|---|---|
| `lexer_array_len` | `10.frontend/core/lexer.spl` | allowlisted (erasure-safe) |
| `rt_array_len_safe` | `10.frontend/core/lexer_struct.spl` | allowlisted |
| `decl_nodes_array_len` | `10.frontend/core/_Ast/decl_nodes.spl` | allowlisted |
| `driver_dict_entry_count` | `80.driver/driver_hir_pipeline_lowering.spl` | **was blocked; now concrete** |

The allowlist is `bootstrap_erased_len_generic_is_safe` in
`declaration_lowering.spl`, gated on `SIMPLE_BOOTSTRAP=1` (exported by
`scripts/bootstrap/bootstrap-from-scratch.sh:1212`). The other 12 generic
functions (`mir_opt/mir_visitor.spl` x7, `core/type_subst.spl`,
`perf/profiler.spl`, `99.loader/unload_ownership.spl` x2) are not in the
closure -- if they were, the gate would have named them too.

Because exactly one call site at exactly one instantiation was blocked,
de-genericising was proportionate; implementing monomorphization for a single
2-line entry counter would not have been.

## What is still blocking Stage 3 (this bug)

### A. `Symbol` registered as both struct and type_alias

Baseline `fa892740806` + the backend/module-lowering fixes, cranelift:

```
error: in-process native-build: HIR lowering error in
src/compiler/driver/driver_source_loading.spl: enum payload dependency `Symbol`
conflicts: `compiler.hir.hir_types::Symbol::struct` vs
`compiler.hir.hir_types::Symbol::type_alias`
```

(emitted twice). Same shape as the `CompiledSymbolKind` / `BackendKind`
duplicate-terminal-declaration bug, but across *kinds* rather than modules:
`Symbol` is declared as `struct Symbol` in `90.tools/query_types.spl` and
`90.tools/sffi_gen/specs/compiler_query.spl`, and as `type Symbol = text` in
`00.common/effects.spl` plus eight `30.types/*` files.
`driver_source_loading.spl` pulls a wildcard `use compiler.types.type_infer.*`.

### B. Nil-receiver crash at origin content

At origin `6fd61352ae7` (which carries a *newer* `module_lowering.spl` than the
baseline above), Stage 3 does not reach a diagnostic list at all:

```
Stage 3: stage2 -> bootstrap_main.spl (self-host)
Illegal instruction (core dumped)
  warning: stage3 self-host failed (exit 132)
stage3-native-build.log: runtime error: field access on nil receiver
```

This is the exact failure mode the TAL3 comment in `module_lowering.spl`
predicts for an alias bound with a nil type
(`define(.., SymbolKind.TypeAlias, nil, ..)`): the name resolves and then the
first field access through it dies. Origin's `module_lowering.spl` is a
different resolution of the same area than the baseline used above, so the two
are not directly comparable -- fixing (A) needs to be done against origin's
version, and (B) triaged first.

## Provenance

Both runs keep the Stage-3 provenance invariant: `stage3-native-build.log`
contains zero of `Build complete: N compiled`, `Linked: ... via clang`, or
`unknown option '...'`, and every `error:` line is prefixed
`in-process native-build:`. Stage 3 is genuinely self-compiling; it is failing
on real diagnostics, not delegating to the Rust seed.

## Reproduce

```sh
sh scripts/bootstrap/bootstrap-from-scratch.sh --backend=cranelift
# log: build/bootstrap/logs/<triple>/stage3-native-build.log
```

LLVM is unavailable in this tree (a plain `cargo build -p simple-driver`
overwrote the seed without `--features llvm`), so `--backend=cranelift` is
required.

## Not landed

`src/compiler/70.backend/backend/hardware_codegen_types.spl` +
`vhdl_backend.spl` carry an unlanded `VhdlProcessKind` ->
`HardwareVhdlProcessKind` rename (there are three `enum VhdlProcessKind`
declarations in the tree: `70.backend/backend/common/hardware_codegen.spl`,
`70.backend/backend/hardware_codegen_types.spl`,
`50.mir/mir_instruction_support.spl`). It was not required by any observed
Stage-3 diagnostic, so it is held rather than pushed speculatively. The full
duplicate-terminal-declaration sweep for `VhdlProcessKind` belongs with (A).
