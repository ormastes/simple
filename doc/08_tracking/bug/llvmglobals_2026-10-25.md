# Cross-module struct field defaults lowered with provider SymbolIds (llvmglobals)

- **Date:** 2026-10-25
- **Status:** workaround landed in source; compiler fix committed, awaiting Stage 2 rebuild to take effect
- **Found by:** Phase 3 run-27e (bootstrap_main closure, base `d3fc04205cf`)
- **Module:** `plugins.backend_llvm_lib.llvm_lib_globals`
- **release/1.0.0:** only the compiler fix (item 2) is ported. `src/plugins/backend_llvm_lib/llvm_lib_globals.spl` does not exist on release/1.0.0, so the source workaround (item 1) does not apply there; the defect in `register_provider_struct` is the same on both lines.

## Symptom

```
[go-to-end] failed stage=mir module=plugins.backend_llvm_lib.llvm_lib_globals:
MIR lowering error: enum construction: unregistered declaration
'compiler.hir.hir_types.compiler.hir.hir_types.SymbolId::is_valid'
at .../src/compiler/50.mir/mir_types.spl:116:30
```

`mir_types.spl:116:30` is the default on `MirStatic`:
`visibility: Visibility = Visibility.Private`. `llvm_lib_globals.spl`
constructs `MirStatic(symbol:, name:, type_:, init:, is_mutable:)` and omits
`visibility`, so MIR lowering fills it from the struct's default expression.

Reproduced in isolation (tiny entry importing only `llvm_lib_globals`, Stage 2
p2shard-17 compiler, direct lane, 10G cap): same message, rc=1, about 5 min.

## Not a missing `use`

`llvm_lib_globals.spl` already imports `compiler.common.dependency.visibility.{Visibility}`.
The bad name is a *method* symbol (`SymbolId::is_valid`) from `hir_types`, which no
source site names. That is what a provider-table SymbolId read through the
consumer's table looks like.

## Root cause (compiler)

Struct default expressions are `HirExpr`s whose `SymbolId`s belong to the
**declaring** module's `SymbolTable`. The direct MIR lane stores them by
**bare struct name** without relocating them:

- `register_module_composite_inventory_v1` (`module_lowering.spl`) writes
  every module's raw `struct_field_default_expr[name]`, keep-first;
- the provider's own `lower_module` overwrites the same bare-name row with
  its raw expressions.

`register_provider_struct` (`provider_metadata.spl`) relocates provider field
*types* into the consumer table but never the defaults. (`register_provider_class`
does relocate class defaults, but `relocate_provider_default` had no `EnumLit`
arm, so an enum default became `Error` there too.) When a consumer omits the
field, `lower_struct_construct` lowers the raw `EnumLit`. `lower_enum_lit`
resolves the provider's `Visibility` id against the consumer table and gets an
unrelated symbol.

## Fix

1. **Workaround** (`llvm_lib_globals.spl`, tagged
   `@workaround bug=llvmglobals_2026-10-25`): pass `visibility: Visibility.Private`
   explicitly. This is the same value the default gives. The `.o` for Phase 3 was
   built from this.
2. **Compiler** (`provider_metadata.spl`, `module_lowering.spl`):
   - `relocate_provider_default` gains an `EnumLit` arm (relocated enum type plus
     relocated payload). It also relocates a **struct** constructor callee
     (`BlockId(id: -1)`) as a type symbol instead of a callable; the callable
     path rejected it as `Error`.
   - `mir_provider_default_children_valid` inspects `EnumLit` payloads.
   - `register_provider_struct` takes the provider `links` and relocates every
     `has_default` field's expression. It writes the relocated rows under the
     layout key and, after the existing bare-layout-owner guards, **overwrites**
     the bare-name `struct_field_has_default` / `struct_field_default_expr` rows.
   - Both callers (eager loop in `lower_module`, demand drain) pass the links. The eager loop now runs after the provider link table is built, because a relocated default can name a provider callable (`AspectParamsV1.defaults()`).

## Blast radius

Census of `src/{compiler,plugins,app,lib,os}`: 675 struct-field defaults; 664 are
literals with no SymbolIds, so they are unaffected. The 11 non-literal ones are:

- enum literals: `MirStatic.visibility`, `CompileOptions.native_cache_mode`;
- enum payload: `HirPerfCostClass.Unknown("...")`;
- struct constructor calls: `BlockId(id: -1)` x2, `SymbolId(id: -1)`,
  `ExtendedCtxRv(bytes: [0; 264])` (an `ArrayRepeat` arm was added for it), `WindowsConsoleDecoderV1()`;
- static method call: `AspectParamsV1.defaults()`.

Before the fix these were read raw: they resolved by luck, or wrongly as here.
After the fix they are relocated. A shape the legacy relocator cannot bind
(lambda, block, `if`/`match`, module-global `Var`) becomes `Error`, and that is
diagnosed only at an omitted-field use site ("unsupported provider default ...;
supply the field explicitly"). After review, the census finds **zero** such struct defaults. Opus review caught that `[0; 264]` (`ArrayRepeat`) would have become `Error`, so an arm was added.

## Known limits

- Demand-mode layout (`provider_layout_demand_active`) relocates only the
  structs it demands. An undemanded provider struct still has its raw inventory
  row.
- The compiler fix takes effect only after a Stage 2 rebuild. It was compiled
  through MIR with the current Stage 2, but its spec was not executed: no test
  runner binary is deployed on this host.
- The bare-name row is cumulative within one lowering session. After
  consumer A relocates it, the row holds A-table ids until the next importer
  re-registers the struct. The provider's own `lower_module` rewrites it raw for
  itself. This is no worse than the old raw provider ids.

## Spec

`test/01_unit/compiler/50.mir/module_composite_inventory_spec.spl`, cases
"relocates a provider struct's enum field default into the consumer table" and
"overwrites the raw bare-name default row only when the consumer does not own the name".
