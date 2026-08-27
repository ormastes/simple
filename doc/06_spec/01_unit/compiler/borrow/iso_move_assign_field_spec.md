# `iso` (Isolated) capability -- reassignment + struct-field-store transfer sites

> Covers two more iso ownership-transfer sites in `mir_lowering_stmts.spl` that

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# `iso` (Isolated) capability -- reassignment + struct-field-store transfer sites

Covers two more iso ownership-transfer sites in `mir_lowering_stmts.spl` that

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/borrow/iso_move_assign_field_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

**Bug:** `doc/08_tracking/bug/iso_transfer_sites_missing_move_return_assign_field_2026-08-06.md`

Covers two more iso ownership-transfer sites in `mir_lowering_stmts.spl` that
were still always-Copy (the let-binding site and the iso call-argument site
were already fixed in prior lanes -- see `iso_move_pipeline_spec.spl` and
`switch_operators_calls.spl`'s `case HirTypeKind.Isolated(_):` call-arg arm):

1. **Reassignment to an existing var** (`b = a`) -- `lower_assign_var`'s plain
   (non-compound) branch, mirrored from the let-binding site's
   `mir_expr_kind_is_place` + `mir_hir_type_is_isolated` guard.
2. **Struct field store** (`obj.f = a`) -- `lower_assign`'s `Field` arm.
   `emit_set_field` takes a bare `MirOperand` with no instruction to hang a
   Move on, so the fix inserts a synthetic `emit_move(fresh, value)` ahead of
   the store (same shape as the already-landed call-argument fix), then
   stores the fresh local instead of the original.

Same hand-built-HIR technique as `iso_move_pipeline_spec.spl` (see that
file's header for why: `iso`/`mut` parameter syntax does not parse through
`parse_full_frontend` yet -- a separate, already-filed pre-existing gap).

## Scenarios

### iso reassignment to an existing var (`b = a`) is a real Move

#### reports a borrow diagnostic for `fn take(a: iso i64) -> i64: var b = 0; b = a; val c = a; 0`

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reports a borrow diagnostic for `fn take(a: iso i64) -> i64: var b = 0; b = a; val c = a; 0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports a borrow diagnostic for `fn take(a: iso i64) -> i64: var b = 0; b = a; val c = a; 0`")
# var b = 0
val let_b0 = HirStmt(kind: HirStmtKind.Let(SymbolId(id: 5), nil, int_lit(0, 9)), span: mk_span(9))
# b = a  -- reassignment: a PLACE read of the iso param into an
# EXISTING var target, the site mir_lowering_stmts.spl:1013 fixes.
val assign_stmt = HirStmt(kind: HirStmtKind.Assign(var_read(SymbolId(id: 5), 15), nil, var_read(SymbolId(id: 1), 15)), span: mk_span(15))
# val c = a  -- use-after-move: must be flagged
val let_c = HirStmt(kind: HirStmtKind.Let(SymbolId(id: 4), nil, var_read(SymbolId(id: 1), 20)), span: mk_span(20))
val fn_ = make_fn([iso_param(SymbolId(id: 1))], [let_b0, assign_stmt, let_c], int_lit(0, 25))
val errors = lower_and_check(fn_)
assert_true(errors.len() > 0)
```

</details>

#### reports no borrow diagnostic for the identical non-iso shape (`a: i64`)

- reports no borrow diagnostic for the identical non-iso shape (`a: i64`)


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports no borrow diagnostic for the identical non-iso shape (`a: i64`)")
val let_b0 = HirStmt(kind: HirStmtKind.Let(SymbolId(id: 5), nil, int_lit(0, 9)), span: mk_span(9))
val assign_stmt = HirStmt(kind: HirStmtKind.Assign(var_read(SymbolId(id: 5), 15), nil, var_read(SymbolId(id: 1), 15)), span: mk_span(15))
val let_c = HirStmt(kind: HirStmtKind.Let(SymbolId(id: 4), nil, var_read(SymbolId(id: 1), 20)), span: mk_span(20))
val fn_ = make_fn([non_iso_param(SymbolId(id: 1))], [let_b0, assign_stmt, let_c], int_lit(0, 25))
val errors = lower_and_check(fn_)
assert_true(errors.len() == 0)
```

</details>

### iso struct field store (`obj.f = a`) is a real Move

#### reports a borrow diagnostic for `fn take(a: iso i64) -> i64: var obj = 0; obj.f = a; val c = a; 0`

- reports a borrow diagnostic for `fn take(a: iso i64) -> i64: var obj = 0; obj.f = a; val c = a; 0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports a borrow diagnostic for `fn take(a: iso i64) -> i64: var obj = 0; obj.f = a; val c = a; 0`")
# var obj = 0  (dummy struct-typed local; resolve_field_index falls
# back to index 0 since symbol 77 is unregistered -- fine, this spec
# only probes the Move-vs-Copy wiring at the store).
val let_obj = HirStmt(kind: HirStmtKind.Let(SymbolId(id: 6), nil, int_lit(0, 9)), span: mk_span(9))
# obj.f = a  -- struct field store of a PLACE read of the iso param,
# the site mir_lowering_stmts.spl's Field arm (emit_set_field) fixes.
val field_assign = HirStmt(kind: HirStmtKind.Assign(field_target(struct_var_read(SymbolId(id: 6), 15), 15), nil, var_read(SymbolId(id: 1), 15)), span: mk_span(15))
# val c = a  -- use-after-move: must be flagged
val let_c = HirStmt(kind: HirStmtKind.Let(SymbolId(id: 4), nil, var_read(SymbolId(id: 1), 20)), span: mk_span(20))
val fn_ = make_fn([iso_param(SymbolId(id: 1))], [let_obj, field_assign, let_c], int_lit(0, 25))
val errors = lower_and_check(fn_)
assert_true(errors.len() > 0)
```

</details>

#### reports no borrow diagnostic for the identical non-iso shape (`a: i64`)

- reports no borrow diagnostic for the identical non-iso shape (`a: i64`)


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports no borrow diagnostic for the identical non-iso shape (`a: i64`)")
val let_obj = HirStmt(kind: HirStmtKind.Let(SymbolId(id: 6), nil, int_lit(0, 9)), span: mk_span(9))
val field_assign = HirStmt(kind: HirStmtKind.Assign(field_target(struct_var_read(SymbolId(id: 6), 15), 15), nil, var_read(SymbolId(id: 1), 15)), span: mk_span(15))
val let_c = HirStmt(kind: HirStmtKind.Let(SymbolId(id: 4), nil, var_read(SymbolId(id: 1), 20)), span: mk_span(20))
val fn_ = make_fn([non_iso_param(SymbolId(id: 1))], [let_obj, field_assign, let_c], int_lit(0, 25))
val errors = lower_and_check(fn_)
assert_true(errors.len() == 0)
```

</details>

### iso array element store (`arr[i] = a`) is a real Move

#### reports a borrow diagnostic for `fn take(a: iso i64) -> i64: var arr = []; arr[0] = a; val c = a; 0`

- reports a borrow diagnostic for `fn take(a: iso i64) -> i64: var arr = []; arr[0] = a; val c = a; 0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports a borrow diagnostic for `fn take(a: iso i64) -> i64: var arr = []; arr[0] = a; val c = a; 0`")
val let_arr = HirStmt(kind: HirStmtKind.Let(SymbolId(id: 8), nil, array_init(9)), span: mk_span(9))
# arr[0] = a  -- array element store of a PLACE read of the iso
# param, the Index arm's plain (non-dict) rt_array_set path fixes.
val arr_assign = HirStmt(kind: HirStmtKind.Assign(index_target(var_read(SymbolId(id: 8), 15), int_lit(0, 15), 15), nil, var_read(SymbolId(id: 1), 15)), span: mk_span(15))
val let_c = HirStmt(kind: HirStmtKind.Let(SymbolId(id: 4), nil, var_read(SymbolId(id: 1), 20)), span: mk_span(20))
val fn_ = make_fn([iso_param(SymbolId(id: 1))], [let_arr, arr_assign, let_c], int_lit(0, 25))
val errors = lower_and_check(fn_)
assert_true(errors.len() > 0)
```

</details>

#### reports no borrow diagnostic for the identical non-iso shape (`a: i64`)

- reports no borrow diagnostic for the identical non-iso shape (`a: i64`)


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports no borrow diagnostic for the identical non-iso shape (`a: i64`)")
val let_arr = HirStmt(kind: HirStmtKind.Let(SymbolId(id: 8), nil, array_init(9)), span: mk_span(9))
val arr_assign = HirStmt(kind: HirStmtKind.Assign(index_target(var_read(SymbolId(id: 8), 15), int_lit(0, 15), 15), nil, var_read(SymbolId(id: 1), 15)), span: mk_span(15))
val let_c = HirStmt(kind: HirStmtKind.Let(SymbolId(id: 4), nil, var_read(SymbolId(id: 1), 20)), span: mk_span(20))
val fn_ = make_fn([non_iso_param(SymbolId(id: 1))], [let_arr, arr_assign, let_c], int_lit(0, 25))
val errors = lower_and_check(fn_)
assert_true(errors.len() == 0)
```

</details>

### iso dict value store (`d[k] = a`) is a real Move

#### reports a borrow diagnostic for `fn take(a: iso i64) -> i64: var d = {}; d[0] = a; val c = a; 0`

- reports a borrow diagnostic for `fn take(a: iso i64) -> i64: var d = {}; d[0] = a; val c = a; 0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports a borrow diagnostic for `fn take(a: iso i64) -> i64: var d = {}; d[0] = a; val c = a; 0`")
val let_d = HirStmt(kind: HirStmtKind.Let(SymbolId(id: 9), nil, dict_init(9)), span: mk_span(9))
# d[0] = a  -- dict value store of a PLACE read of the iso param,
# the Index arm's dict (rt_dict_set) path fixes.
val dict_assign = HirStmt(kind: HirStmtKind.Assign(index_target(var_read(SymbolId(id: 9), 15), int_lit(0, 15), 15), nil, var_read(SymbolId(id: 1), 15)), span: mk_span(15))
val let_c = HirStmt(kind: HirStmtKind.Let(SymbolId(id: 4), nil, var_read(SymbolId(id: 1), 20)), span: mk_span(20))
val fn_ = make_fn([iso_param(SymbolId(id: 1))], [let_d, dict_assign, let_c], int_lit(0, 25))
val errors = lower_and_check(fn_)
assert_true(errors.len() > 0)
```

</details>

#### reports no borrow diagnostic for the identical non-iso shape (`a: i64`)

- reports no borrow diagnostic for the identical non-iso shape (`a: i64`)


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports no borrow diagnostic for the identical non-iso shape (`a: i64`)")
val let_d = HirStmt(kind: HirStmtKind.Let(SymbolId(id: 9), nil, dict_init(9)), span: mk_span(9))
val dict_assign = HirStmt(kind: HirStmtKind.Assign(index_target(var_read(SymbolId(id: 9), 15), int_lit(0, 15), 15), nil, var_read(SymbolId(id: 1), 15)), span: mk_span(15))
val let_c = HirStmt(kind: HirStmtKind.Let(SymbolId(id: 4), nil, var_read(SymbolId(id: 1), 20)), span: mk_span(20))
val fn_ = make_fn([non_iso_param(SymbolId(id: 1))], [let_d, dict_assign, let_c], int_lit(0, 25))
val errors = lower_and_check(fn_)
assert_true(errors.len() == 0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ac0b87ec0c18c91c6192654ffee2d60fa8e71e867142a65aaa8f67f2ba40a8ec`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ac0b87ec0c18c91c6192654ffee2d60fa8e71e867142a65aaa8f67f2ba40a8ec`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ac0b87ec0c18c91c6192654ffee2d60fa8e71e867142a65aaa8f67f2ba40a8ec`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/borrow/iso_move_assign_field_spec.spl
mirror: doc/06_spec/01_unit/compiler/borrow/iso_move_assign_field_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/borrow/iso_move_assign_field_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/borrow/iso_move_assign_field_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/borrow/iso_move_assign_field_spec.spl:160:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports a borrow diagnostic for `fn take(a: iso i64) -> i64: var b = 0; b = a; val c = a; 0`' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/borrow/iso_move_assign_field_spec.spl:174:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports no borrow diagnostic for the identical non-iso shape (`a: i64`)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/borrow/iso_move_assign_field_spec.spl:185:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports a borrow diagnostic for `fn take(a: iso i64) -> i64: var obj = 0; obj.f = a; val c = a; 0`' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
