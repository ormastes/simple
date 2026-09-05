# `iso` (Isolated) capability -- real MIR-lowering move-through-the-pipeline specs

> An earlier version of this spec drove real `iso`/`mut` source text through

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# `iso` (Isolated) capability -- real MIR-lowering move-through-the-pipeline specs

An earlier version of this spec drove real `iso`/`mut` source text through

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/borrow/iso_move_pipeline_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Why this spec hand-builds HIR instead of parsing `iso` source text

An earlier version of this spec drove real `iso`/`mut` source text through
`parse_full_frontend` (the same real parser `CompilerDriver` uses), matching
the syntax shown throughout
test/03_system/feature/usage/capability_system_spec.spl (e.g.
`fn transfer(data: iso i64) -> i64:`). That is RED even after this lane's
change, and RED the same way for `mut` too -- confirmed by direct repro:

```
$ fn take(a: iso i64) -> i64:\n    a\n   -> [parser_error] ... expected ), got Ident 'i64'
$ fn take(a: mut i64) -> i64:\n    a\n   -> [parser_error] ... expected ), got Ident 'i64'
```

`parse_full_frontend`'s parameter-type grammar has no construction site for
`TypeKind.Isolated`/`TypeKind.Atomic` at all (confirmed by repo-wide grep:
zero non-declaration references to `TypeKind.Isolated`/`TypeKind.Atomic` in
`src/compiler/10.frontend/**`, versus 2 references in the treesitter OUTLINE
parser, a separate lighter-weight pass used for LSP/docs, not compilation).
It parses the bare `iso`/`mut` token as an ordinary type NAME and then
chokes on the following identifier. This is a **pre-existing parser-layer
gap**, upstream of everything HIR/MIR/borrow-check touches, and out of this
lane's scope (`.claude/rules` requires a bug record rather than silently
working around a real gap -- filed as
`doc/08_tracking/bug/iso_mut_capability_prefix_not_parsed_2026-07-29.md`).
It also means `capability_system_spec.spl`'s "40/40 passed" does NOT
exercise `parse_full_frontend` for its `iso`/`mut` examples (that spec's
`it` bodies run through the test-runner's interpreter path, not the real
compiler frontend) -- a separate testing-integrity finding recorded in the
same bug doc.

To prove this lane's own mechanism -- that a real (non-erased)
`HirTypeKind.Isolated` on a parameter's type survives MIR lowering into a
genuine `Move` instruction at a variable-to-variable let-binding, and that
the real (non-hand-built) `check_mir_module` reports it -- this spec hand-
builds a small HIR function directly (mirroring
test/01_unit/compiler/mir/mir_span_thread_spec.spl's own justification for
doing the same, there for a different pre-existing gap: AST span
population). This isolates HIR/MIR-lowering-side correctness from the
separately-broken parser-side gap.

## Scenarios

### iso use-after-move (red-line probe)

#### reports a borrow diagnostic for `fn take(a: iso i64) -> i64: val b = a; val c = a; 0` (real MIR lowering + real NLL checker, hand-built HIR)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reports a borrow diagnostic for `fn take(a: iso i64) -> i64: val b = a; val c = a; 0` (real MIR lowering + real NLL checker, hand-built HIR)


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports a borrow diagnostic for `fn take(a: iso i64) -> i64: val b = a; val c = a; 0` (real MIR lowering + real NLL checker, hand-built HIR)")
# val b = a   -- the move
val let_b = HirStmt(kind: HirStmtKind.Let(SymbolId(id: 2), nil, var_read(SymbolId(id: 1), 10)), span: mk_span(10))
# val c = a   -- the use-after-move: a second place-read of the
# already-moved iso source. An iso place is move-only (it can never
# emit a plain Copy — see mir_lowering_stmts.spl's
# mir_hir_type_is_isolated wiring), so THIS, not a bare trailing
# `a` read (which the checker's terminator conversion does not see
# at all — MirTerminator.Ret(_) drops its operand, a pre-
# existing, separate blind spot left as-is), is the real shape an
# iso use-after-move program lowers to.
val let_c = HirStmt(kind: HirStmtKind.Let(SymbolId(id: 4), nil, var_read(SymbolId(id: 1), 20)), span: mk_span(20))
val fn_ = make_take_fn([let_b, let_c], int_lit(0, 25))
val errors = lower_and_check(fn_)
assert_true(errors.len() > 0)
```

</details>

### iso moved then reassigned then used (kill-on-reassign)

#### reports no borrow diagnostic when the iso parameter is reassigned before its next use

- reports no borrow diagnostic when the iso parameter is reassigned before its next use


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports no borrow diagnostic when the iso parameter is reassigned before its next use")
# val b = a
val let_b = HirStmt(kind: HirStmtKind.Let(SymbolId(id: 2), nil, var_read(SymbolId(id: 1), 10)), span: mk_span(10))
# a = 2   (plain reassignment -- op: nil -- kills the moved state)
val assign_stmt = HirStmt(kind: HirStmtKind.Assign(var_read(SymbolId(id: 1), 15), nil, int_lit(2, 15)), span: mk_span(15))
# val c = a   -- read after re-init, must be clean
val let_c = HirStmt(kind: HirStmtKind.Let(SymbolId(id: 4), nil, var_read(SymbolId(id: 1), 20)), span: mk_span(20))
val fn_ = make_take_fn([let_b, assign_stmt, let_c], int_lit(0, 25))
val errors = lower_and_check(fn_)
assert_true(errors.len() == 0)
```

</details>

### identical non-iso code is unaffected

#### reports no borrow diagnostic for the same shape (`fn take(a: i64) -> i64: val b = a; val c = a; 0`) without `iso`

- reports no borrow diagnostic for the same shape (`fn take(a: i64) -> i64: val b = a; val c = a; 0`) without `iso`


<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports no borrow diagnostic for the same shape (`fn take(a: i64) -> i64: val b = a; val c = a; 0`) without `iso`")
val non_iso_param = HirParam(symbol: SymbolId(id: 1), name: "a", type_: i64_type(), has_default: false, default: nil_expr(), span: mk_span(0), is_mutable: false)
val let_b = HirStmt(kind: HirStmtKind.Let(SymbolId(id: 2), nil, var_read(SymbolId(id: 1), 10)), span: mk_span(10))
val let_c = HirStmt(kind: HirStmtKind.Let(SymbolId(id: 4), nil, var_read(SymbolId(id: 1), 20)), span: mk_span(20))
val body = HirBlock(stmts: [let_b, let_c], has: true, value: int_lit(0, 25), span: mk_span(1))
val fn_ = HirFunction(
    symbol: SymbolId(id: 3),
    name: "take",
    type_params: [],
    params: [non_iso_param],
    return_type: i64_type(),
    body: body,
    effects: [],
    visibility: Visibility.Public,
    is_async: false,
    is_static: false,
    is_public: true,
    is_method: false,
    is_mutable: false,
    is_const: false,
    is_extern: false,
    func_attr: FunctionAttr.default(),
    has_export_attr: false,
    export_attr: nil,
    has_driver_manifest_attr: false,
    driver_manifest_attr: nil,
    has_suspension: false,
    has_vhdl_metadata: false,
    vhdl_metadata: nil,
    has_doc_comment: false,
    doc_comment: "",
    span: mk_span(1)
)
val errors = lower_and_check(fn_)
assert_true(errors.len() == 0)
```

</details>

### iso struct binding is a move, not a copy (WP-F0, 2026-08-06)

#### reports a borrow diagnostic for `fn take(a: iso Task) -> i64: val b = a; val c = a; 0` (struct-typed iso param, real MIR lowering + real NLL checker)

- reports a borrow diagnostic for `fn take(a: iso Task) -> i64: val b = a; val c = a; 0` (struct-typed iso param, real MIR lowering + real NLL checker)


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports a borrow diagnostic for `fn take(a: iso Task) -> i64: val b = a; val c = a; 0` (struct-typed iso param, real MIR lowering + real NLL checker)")
val struct_sym = SymbolId(id: 5)
val task_struct = make_task_struct(struct_sym)
# val b = a   -- the move
val let_b = HirStmt(kind: HirStmtKind.Let(SymbolId(id: 2), nil, var_read(SymbolId(id: 1), 10)), span: mk_span(10))
# val c = a   -- use-after-move of the already-moved iso struct source
val let_c = HirStmt(kind: HirStmtKind.Let(SymbolId(id: 4), nil, var_read(SymbolId(id: 1), 20)), span: mk_span(20))
val fn_ = make_take_struct_fn(struct_sym, [let_b, let_c], int_lit(0, 25))
val errors = lower_and_check_struct(fn_, struct_sym, task_struct)
assert_true(errors.len() > 0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `af3cf4da8f934d5633d4df889450aac1e92267ed707d9d634bb50175c4846bce`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `af3cf4da8f934d5633d4df889450aac1e92267ed707d9d634bb50175c4846bce`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `af3cf4da8f934d5633d4df889450aac1e92267ed707d9d634bb50175c4846bce`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/borrow/iso_move_pipeline_spec.spl
mirror: doc/06_spec/01_unit/compiler/borrow/iso_move_pipeline_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/borrow/iso_move_pipeline_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/borrow/iso_move_pipeline_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/borrow/iso_move_pipeline_spec.spl:294:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports a borrow diagnostic for `fn take(a: iso i64) -> i64: val b = a; val c = a; 0` (real MIR lowering + real NLL checker, hand-built HIR)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/borrow/iso_move_pipeline_spec.spl:313:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports no borrow diagnostic when the iso parameter is reassigned before its next use' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/borrow/iso_move_pipeline_spec.spl:327:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports no borrow diagnostic for the same shape (`fn take(a: i64) -> i64: val b = a; val c = a; 0`) without `iso`' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
