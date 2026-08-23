# HIR construct coverage matrix (2026-08-23)

**Scope:** `src/compiler/20.hir/**` + the `src/compiler/10.frontend/_FlatAstBridge/**` bridge.
**Method:** construct list derived from the CODE (every variant of every enum declared under those trees), cross-checked against `spec/compiler_schema/registry/`.
**New specs:** `test/01_unit/compiler/hir/ast_to_hir_construct_coverage_spec.spl` (71 rows, GREEN) and `test/01_unit/compiler/hir/hir_lowering_construct_gaps_spec.spl` (6 rows, RED by design).

## 0. Headline numbers

| | count |
|---|---|
| enums declared under the HIR scope | 29 |
| variants across those enums | 290 |
| variants with NO reference in any HIR/frontend/transition spec before this change | 107 |
| variants with no construction site anywhere in `20.hir` | 26 |
| variants now pinned by a NEW executable lowering test | 58 |
| source defects found and filed | 6 |

## 1. Structural findings (read these first)

### 1.1 The AST -> HIR boundary has no transition table

`spec/compiler_schema/transitions/` carries `flat_decl_to_ast_decl`, `flat_expr_to_ast_expr`,
`flat_stmt_to_ast_stmt`, `hir_expr_to_mir`, `hir_stmt_to_mir`, `hir_type_to_mir_type`, and
nine MIR-to-backend tables. There is **no `ast_*_to_hir_*` table**. AST -> HIR is the single
un-tabulated hop in the whole pipeline, and it is precisely where this session's stage1
failures lived. Every other boundary has a totality proof; this one had none.

### 1.2 Only 4 of 29 HIR enums are in the schema registry

Registered and verified byte-consistent with the code (code == registry == declared count):

| enum | code | registry | declared |
|---|---|---|---|
| `HirExprKind` | 57 | 57 | 57 |
| `HirPatternKind` | 13 | 13 | 13 |
| `HirStmtKind` | 5 | 5 | 5 |
| `HirTypeKind` | 27 | 27 | 27 |

**No discrepancy found** between code and registry for those four -- the registry is honest.
The finding is what is ABSENT: 25 further HIR enums have no registry row and therefore no
totality gate at all, including the operator families that carry the most variants:
`HirBinOp` (35), `SymbolKind` (15), `HirAssignOp` (10), `Type` (29, inference),
`DimExprKind` (9), `EffectKind` (7), `HirUnaryOp` (7), `ScopeKind` (7),
`LoweringErrorKind` (7), `MethodResolution` (5), `MemorySpace` (5),
`HirContractClauseKind` (5), `HirComprehensionKind` (4), `Constraint` (4), `InferError` (4),
`HirNode` (4), `HirWalkNode` (4), `AsyncErrorCode` (10), `HirVariantKind` (3),
`UnifyError` (3), `DeviceType` (3), `HirCompClauseKind` (2), `HirContractOutcome` (2),
`HirEnumPayload` (2), `HirPatternPayload` (2).

### 1.3 Existing HIR specs that have never executed

`test/01_unit/compiler/hir/member_visibility_enforcement_spec.spl` -- the spec covering the
exact defect class that produced 1412 errors from one hardcoded-visibility line -- imports
`compiler.frontend.parser_types.Module`, a symbol that does not exist (the struct is
`ParserModule`). It errors before executing a single example:

```
SPEC FILE VERDICT: .../member_visibility_enforcement_spec.spl outcome=ERROR declared>=15 executed=0 passed=0 failed=0
error: runtime: Module "compiler.frontend.parser_types" does not export 'Module'
```

It also calls `parse_full_frontend(source, module_name, file_path, log)` with `file_path`
and `module_name` transposed relative to the real signature
`parse_full_frontend(source: text, file_path: text, module_name: text, log: Logger)`.
Filed as `doc/08_tracking/bug/hir_specs_stale_parser_module_import_2026-08-23.md`.

## 2. Construct matrix -- HirExprKind (57)

Legend: **PINNED** = a new row in the census spec runs the real lowering and asserts the
emitted kind. **DESUGARED** = probed, the construct lowers to a different variant (the row
pins the observed kind instead). **UNPROBED** = no snippet in this battery; genuinely
unverified.

| # | variant | status | evidence / emitted instead |
|---|---|---|---|
| 1 | `IntLit` | PINNED | census spec row (real lowering) |
| 2 | `FloatLit` | PINNED | census spec row (real lowering) |
| 3 | `StringLit` | PINNED | census spec row (real lowering) |
| 4 | `BoolLit` | PINNED | census spec row (real lowering) |
| 5 | `CharLit` | DESUGARED | emits StringLit  (`'a'`) |
| 6 | `UnitLit` | DESUGARED | emits NilLit  (`()`) |
| 7 | `NilLit` | PINNED | census spec row (real lowering) |
| 8 | `ArrayLit` | PINNED | census spec row (real lowering) |
| 9 | `ArrayRepeat` | PINNED | census spec row (real lowering) |
| 10 | `TupleLit` | PINNED | census spec row (real lowering) |
| 11 | `DictLit` | PINNED | census spec row (real lowering) |
| 12 | `SetLit` | DESUGARED | emits HirTypeKind.Error + NilLit  (`#{1,2}`) -- DEFECT |
| 13 | `Var` | PINNED | census spec row (real lowering) |
| 14 | `NamedVar` | PINNED | census spec row (real lowering) |
| 15 | `Field` | PINNED | census spec row (real lowering) |
| 16 | `Index` | PINNED | census spec row (real lowering) |
| 17 | `TupleIndex` | DESUGARED | emits Index  (`t.0`) |
| 18 | `OptionalChain` | DESUGARED | emits Field  (`s?.a`) |
| 19 | `NullCoalesce` | PINNED | census spec row (real lowering) |
| 20 | `ExistsCheck` | DESUGARED | emits Try  (`a?`) |
| 21 | `Unwrap` | PINNED | census spec row (real lowering) |
| 22 | `Binary` | PINNED | census spec row (real lowering) |
| 23 | `Unary` | PINNED | census spec row (real lowering) |
| 24 | `Call` | PINNED | census spec row (real lowering) |
| 25 | `MethodCall` | PINNED | census spec row (real lowering) |
| 26 | `StaticCall` | DESUGARED | emits MethodCall  (`S.make()`) |
| 27 | `If` | DESUGARED | emits IfChain  (plain `if/else`; If reachable only via desugarings) |
| 28 | `IfChain` | PINNED | census spec row (real lowering) |
| 29 | `MatchCase` | PINNED | census spec row (real lowering) |
| 30 | `Loop` | DESUGARED | emits While(true)  (`loop:`) |
| 31 | `While` | PINNED | census spec row (real lowering) |
| 32 | `For` | PINNED | census spec row (real lowering) |
| 33 | `With` | UNPROBED | 2 construction site(s) in 20.hir |
| 34 | `Lambda` | PINNED | census spec row (real lowering) |
| 35 | `Block` | PINNED | census spec row (real lowering) |
| 36 | `HostGpuLane` | UNPROBED | 3 construction site(s) in 20.hir |
| 37 | `Return` | PINNED | census spec row (real lowering) |
| 38 | `Break` | PINNED | census spec row (real lowering) |
| 39 | `Continue` | PINNED | census spec row (real lowering) |
| 40 | `Throw` | DESUGARED | emits Call + HirExprKind.Error  (`throw "bad"`) -- DEFECT |
| 41 | `Try` | PINNED | census spec row (real lowering) |
| 42 | `Await` | UNPROBED | 3 construction site(s) in 20.hir |
| 43 | `Yield` | PINNED | census spec row (real lowering) |
| 44 | `StructLit` | DESUGARED | emits Call  (`S(a: 1)`) |
| 45 | `EnumLit` | DESUGARED | emits Field  (`E.A`) |
| 46 | `Cast` | PINNED | census spec row (real lowering) |
| 47 | `As` | UNPROBED | 1 construction site(s) in 20.hir |
| 48 | `Range` | PINNED | census spec row (real lowering) |
| 49 | `Comprehension` | PINNED | census spec row (real lowering) |
| 50 | `CustomBlock` | UNPROBED | 3 construction site(s) in 20.hir |
| 51 | `LossBlock` | UNPROBED | 2 construction site(s) in 20.hir |
| 52 | `NogradBlock` | UNPROBED | 2 construction site(s) in 20.hir |
| 53 | `UnsafeBlock` | PINNED | census spec row (real lowering) |
| 54 | `InlineAsm` | UNPROBED | 2 construction site(s) in 20.hir |
| 55 | `InlineAsmMatch` | UNPROBED | 2 construction site(s) in 20.hir |
| 56 | `Error` | UNPROBED | 5 construction site(s) in 20.hir |
| 57 | `TypeTest` | PINNED | census spec row (real lowering) |

## 3. Construct matrix -- HirPatternKind (13)

| # | variant | status | evidence / emitted instead |
|---|---|---|---|
| 1 | `Wildcard` | PINNED | census spec row (real lowering) |
| 2 | `Literal` | PINNED | census spec row (real lowering) |
| 3 | `Binding` | PINNED | census spec row (real lowering) |
| 4 | `Tuple` | DESUGARED | emits Block of Let+Index  (`case (a, b)`) |
| 5 | `Array` | DESUGARED | emits Wildcard + HirExprKind.Error  (`case [a, b]`) -- DEFECT |
| 6 | `Struct` | DESUGARED | emits Block of Let+Field  (`case S(a)`) |
| 7 | `Enum` | PINNED | census spec row (real lowering) |
| 8 | `Or` | PINNED | census spec row (real lowering) |
| 9 | `Range` | DESUGARED | emits If comparison  (`case 1..3`) |
| 10 | `Error` | UNPROBED | 2 construction site(s) in 20.hir |
| 11 | `CompleteRegion` | UNPROBED | 3 construction site(s) in 20.hir |
| 12 | `DynRegion` | UNPROBED | 3 construction site(s) in 20.hir |
| 13 | `TypeTest` | UNPROBED | 3 construction site(s) in 20.hir |

## 4. Construct matrix -- HirStmtKind (5)

| # | variant | status | evidence / emitted instead |
|---|---|---|---|
| 1 | `Expr` | PINNED | census spec row (real lowering) |
| 2 | `Let` | PINNED | census spec row (real lowering) |
| 3 | `Assign` | PINNED | census spec row (real lowering) |
| 4 | `Block` | UNPROBED | 2 construction site(s) in 20.hir |
| 5 | `AsmAssert` | UNPROBED | 2 construction site(s) in 20.hir |

## 5. Construct matrix -- HirTypeKind (27)

| # | variant | status | evidence / emitted instead |
|---|---|---|---|
| 1 | `Int` | PINNED | census spec row (real lowering) |
| 2 | `Float` | PINNED | census spec row (real lowering) |
| 3 | `Bool` | PINNED | census spec row (real lowering) |
| 4 | `Char` | PINNED | census spec row (real lowering) |
| 5 | `Str` | PINNED | census spec row (real lowering) |
| 6 | `Unit` | PINNED | census spec row (real lowering) |
| 7 | `Tuple` | PINNED | census spec row (real lowering) |
| 8 | `Array` | PINNED | census spec row (real lowering) |
| 9 | `Slice` | DESUGARED | emits Array  (`[T]`) |
| 10 | `Dict` | PINNED | census spec row (real lowering) |
| 11 | `Ref` | PINNED | census spec row (real lowering) |
| 12 | `Ptr` | PINNED | census spec row (real lowering) |
| 13 | `Optional` | PINNED | census spec row (real lowering) |
| 14 | `Result` | UNPROBED | 5 construction site(s) in 20.hir |
| 15 | `Named` | PINNED | census spec row (real lowering) |
| 16 | `TypeParam` | DESUGARED | emits Named  (`fn f<T>(a: T)`) -- generic params never reach TypeParam |
| 17 | `Union` | PINNED | census spec row (real lowering) |
| 18 | `DynTrait` | DESUGARED | emits Named  (`dyn Tr`) |
| 19 | `Function` | DESUGARED | emits Any  (`fn(i64) -> i64`) -- DEFECT, declared type erased |
| 20 | `Projection` | UNPROBED | 2 construction site(s) in 20.hir |
| 21 | `Isolated` | UNPROBED | 2 construction site(s) in 20.hir |
| 22 | `Infer` | UNPROBED | 8 construction site(s) in 20.hir |
| 23 | `Error` | UNPROBED | 10 construction site(s) in 20.hir |
| 24 | `Never` | DESUGARED | emits HirTypeKind.Error  (`never`) -- DEFECT, unresolved type |
| 25 | `Any` | PINNED | census spec row (real lowering) |
| 26 | `Tensor` | UNPROBED | 1 construction site(s) in 20.hir |
| 27 | `Layer` | UNPROBED | 1 construction site(s) in 20.hir |

## 6. The remaining 25 unregistered enums

None of these is pinned by a lowering test. All are listed here by name so the gap is
explicit rather than implied.

| enum | variants | variants with zero construction site in 20.hir |
|---|---|---|
| `AsyncErrorCode` | 10 | `E0803`, `E0806` |
| `Constraint` | 4 | `Subtype` |
| `DeviceType` | 3 | -- |
| `DimExprKind` | 9 | -- |
| `EffectKind` | 7 | -- |
| `HirAssignOp` | 10 | -- |
| `HirBinOp` | 35 | -- |
| `HirCompClauseKind` | 2 | -- |
| `HirComprehensionKind` | 4 | -- |
| `HirContractClauseKind` | 5 | -- |
| `HirContractOutcome` | 2 | -- |
| `HirEnumPayload` | 2 | -- |
| `HirNode` | 4 | -- |
| `HirPatternPayload` | 2 | -- |
| `HirUnaryOp` | 7 | -- |
| `HirVariantKind` | 3 | -- |
| `HirWalkNode` | 4 | -- |
| `InferError` | 4 | `Undefined`, `NotCallable`, `FieldNotFound` |
| `LoweringErrorKind` | 7 | `UnresolvedName`, `DuplicateDefinition`, `TypeMismatch`, `InvalidPattern`, `InvalidExpression` |
| `MemorySpace` | 5 | `Global`, `Shared`, `Local`, `Constant`, `Uniform` |
| `MethodResolution` | 5 | -- |
| `ScopeKind` | 7 | -- |
| `SymbolKind` | 15 | -- |
| `Type` | 29 | `Skolem`, `Struct`, `Enum`, `Class`, `TypeParam`, `DynTrait`, `ConstKeySet`, `DependentKeys`, `Constructor`, `Deferred` |
| `UnifyError` | 3 | -- |

## 7. Defects found (all filed, all RED)

`test/01_unit/compiler/hir/hir_lowering_construct_gaps_spec.spl` asserts the CORRECT behaviour for each and is expected to fail until fixed:

| # | construct | observed | why it matters |
|---|---|---|---|
| 1 | `never` return type | lowers to `HirTypeKind.Error` | `HirTypeKind.Never` exists in the registry and is unreachable; this is the `unresolved type` class that cost hours in stage1 |
| 2 | `fn(i64) -> i64` param type | erased to `HirTypeKind.Any` | a DECLARED type is silently discarded; `HirTypeKind.Function` is unreachable |
| 3 | enum payload pattern binder | typed `HirTypeKind.Error` | `case A(v)` gives `v` an Error type -- the type-alias resolution gap class |
| 4 | array pattern `case [a, b]` | emits `HirExprKind.Error` | an Error EXPRESSION node inside a well-formed program |
| 5 | set literal `#{1, 2}` | `HirTypeKind.Error` + `NilLit` | `HirExprKind.SetLit` is unreachable; set literals do not lower |
| 6 | `throw "bad"` | emits `HirExprKind.Error` | an Error node in a well-formed function; `HirExprKind.Throw` is unreachable |

## 8. Discrimination evidence (neuter runs)

Every row of the census spec was authored from an EMPIRICAL probe of the real lowering, not
from the enum name, so no row can pass by naming a variant that is never emitted. Three
independent neuter runs, one per HIR layer, confirm the rows fail when the responsible
lowering arm is broken -- and confirm the rows are INDEPENDENT (only the targeted rows move):

```
# baseline
Results: 71 total, 71 passed, 0 failed

# neuter 1 (expression layer): expression_core.spl:492 Cast -> Unary,
#                              expression_core.spl:489 Unwrap -> NullCoalesce
  x `!` lowers to Unwrap
  x `as` lowers to Cast
Results: 71 total, 69 passed, 2 failed

# neuter 2 (pattern layer): expression_components.spl:282 HirPatternKind.Or -> Wildcard
  x an or-pattern lowers to Or
Results: 71 total, 70 passed, 1 failed

# neuter 3 (type layer): types.spl:728,744 HirTypeKind.Optional -> HirTypeKind.Any
  x an optional type lowers to Optional
Results: 71 total, 70 passed, 1 failed
```

All three neuters were reverted and the baseline re-verified before commit.

## 9. Named list of constructs still UNVERIFIED

These have no executable lowering test after this change. Listed so the map is truthful:

- **HirExprKind (10):** `With`, `HostGpuLane`, `Await`, `As`, `CustomBlock`, `LossBlock`, `NogradBlock`, `InlineAsm`, `InlineAsmMatch`, `Error`
- **HirPatternKind (4):** `Error`, `CompleteRegion`, `DynRegion`, `TypeTest`
- **HirStmtKind (2):** `Block`, `AsmAssert`
- **HirTypeKind (7):** `Result`, `Projection`, `Isolated`, `Infer`, `Error`, `Tensor`, `Layer`
- **All 25 unregistered enums (233 variants):** see section 6.

## 10. Harness

The census runs the REAL path, not a helper:

```
parse_full_frontend(source, file_path, module_name, log)   # 10.frontend
  -> module_surfaces_from_modules(modules, sources)        # 20.hir module surface registry
  -> hirlowering_for_module(path, surfaces)                # 20.hir HirLowering
  -> lowering.lower_module(parsed) -> HirModule            # 20.hir _Items/module_lowering
  -> walk_hir_type / walk_hir_block                        # 20.hir/generated/hir_visitor
```

Parameter types, the return type, and the full statement/expression/pattern tree of every
lowered function are walked, so a construct that only appears in a signature is reachable.
