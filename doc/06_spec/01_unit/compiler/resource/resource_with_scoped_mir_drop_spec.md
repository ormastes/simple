# `with EXPR as NAME:` MIR drop/close edges -- WP-K acceptance (runtime side)

> Purpose: Prove that with-desugar (b): normal BODY fall-through reaches the appended `x.close()`.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# `with EXPR as NAME:` MIR drop/close edges -- WP-K acceptance (runtime side)

Purpose: Prove that with-desugar (b): normal BODY fall-through reaches the appended `x.close()`.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Plan | doc/03_plan/language/resource/resource_parallel_agent_plan_2026-08-06.md (WP-K) |
| Source | `test/01_unit/compiler/resource/resource_with_scoped_mir_drop_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that with-desugar (b): normal BODY fall-through reaches the appended `x.close()`.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### with-desugar (b): normal BODY fall-through reaches the appended `x.close()`

#### lowers `val x = ACQUIRE; print-ish BODY; x.close()` to exactly one Drop, on the close() site

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- lowers `val x = ACQUIRE; print-ish BODY; x.close()` to exactly one Drop, on the close() site
- Verify: lowers `val x = ACQUIRE; print-ish BODY; x.close()` to exactly one Drop, on the close() site
   - Expected: count_drops(fn_result) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("lowers `val x = ACQUIRE; print-ish BODY; x.close()` to exactly one Drop, on the close() site")
step("Verify: lowers `val x = ACQUIRE; print-ish BODY; x.close()` to exactly one Drop, on the close() site")
# @req: REQ-COMPILER-RESOURCE-001
val (table, res_sym) = setup()
val x_sym = SymbolId(id: 1)
val let_stmt = with_let_stmt(x_sym, res_sym, 10)
val body_stmt = expr_stmt(int_lit(1, 11), 11)  # stand-in for an arbitrary BODY statement
val close = close_stmt(x_sym, 12)
val fn_ = make_fn([], [let_stmt, body_stmt, close], int_lit(0, 13), 5)
var lowering = MirLowering.new(table)
val fn_result = lowering.lower_function(fn_)
# Exactly one Drop total: the `.close()` call itself. The
# function-end scope-exit sweep must NOT double-drop the
# now-consumed `x`.
expect(count_drops(fn_result)).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

### with-desugar (c): an explicit `return` inside BODY

#### drops the FRESH with-bound resource before the explicit return, without a param or a move

- drops the FRESH with-bound resource before the explicit return, without a param or a move
- Verify: drops the FRESH with-bound resource before the explicit return, without a param or a move
   - Expected: count_drops(fn_result) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("drops the FRESH with-bound resource before the explicit return, without a param or a move")
step("Verify: drops the FRESH with-bound resource before the explicit return, without a param or a move")
# Deliberately NO trailing close() statement in this variant --
# `.close()`'s own Drop emission (method_calls_literals.spl) is
# type-check-based, not resource_owned_locals-based, so a close()
# placed after `return` would (structurally) still lower into its
# own block and satisfy `count_drops == 1` on its own, silently
# masking whether the RETURN path's drop-edge (the thing this case
# is actually about) fired at all. Isolate the return-path
# mechanism the same way WP-E's own explicit-return spec does.
val (table, res_sym) = setup()
val x_sym = SymbolId(id: 1)
val let_stmt = with_let_stmt(x_sym, res_sym, 10)
val ret = return_stmt(0, 11)
val fn_ = make_fn_stmts_only([], [let_stmt, ret], 5)
var lowering = MirLowering.new(table)
val fn_result = lowering.lower_function(fn_)
# One Drop on the return path.
expect(count_drops(fn_result)).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

### with-desugar (d): a `?` early-return INSIDE BODY (not on the acquire)

#### drops the with-bound resource on the `?` Err path, independent of the acquire

- drops the with-bound resource on the `?` Err path, independent of the acquire
- Verify: drops the with-bound resource on the `?` Err path, independent of the acquire
   - Expected: count_drops_in_block(fn_result, "try_err") equals `1`
   - Expected: count_drops_in_block(fn_result, "try_ok") equals `1`
   - Expected: count_drops(fn_result) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("drops the with-bound resource on the `?` Err path, independent of the acquire")
step("Verify: drops the with-bound resource on the `?` Err path, independent of the acquire")
val (table, res_sym) = setup()
val x_sym = SymbolId(id: 1)
val code_sym = SymbolId(id: 2)
val code_param = plain_param(code_sym, "code")
val let_stmt = with_let_stmt(x_sym, res_sym, 10)
# BODY's tail is a `?` on an UNRELATED value (not the acquired
# resource) -- models `with r.open() as x: some_other_call()?`.
val try_tail = HirExpr(kind: HirExprKind.Try(var_read(code_sym, 12)), has_type_: true, type_: i64_type(), span: mk_span(12))
val fn_ = make_fn([code_param], [let_stmt], try_tail, 5)
var lowering = MirLowering.new(table)
val fn_result = lowering.lower_function(fn_)
# One drop on the `?` Err early-return path, one more on the
# separate Ok fall-through path (per-branch drop edges, same
# "different blocks, same forward pass" property WP-E's own `?`
# spec documents) -- both reachable, both owed, x was never
# consumed by a close() on this variant.
expect(count_drops_in_block(fn_result, "try_err")).to_equal(1)
expect(count_drops_in_block(fn_result, "try_ok")).to_equal(1)
expect(count_drops(fn_result)).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

### with-desugar (e): a failed ACQUIRE never binds anything

#### registers/drops NOTHING on the `?` Err path when the `?` is inside the ACQUIRE itself

- registers/drops NOTHING on the `?` Err path when the `?` is inside the ACQUIRE itself
- Verify: registers/drops NOTHING on the `?` Err path when the `?` is inside the ACQUIRE itself
   - Expected: count_drops_in_block(fn_result, "try_err") equals `0`
   - Expected: count_drops(fn_result) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("registers/drops NOTHING on the `?` Err path when the `?` is inside the ACQUIRE itself")
step("Verify: registers/drops NOTHING on the `?` Err path when the `?` is inside the ACQUIRE itself")
val (table, res_sym) = setup()
val x_sym = SymbolId(id: 1)
val code_sym = SymbolId(id: 2)
val code_param = plain_param(code_sym, "code")
# `with R.open(...)? as x:` -- the `?` is INSIDE the val's own
# initializer. Its Err early-return fires strictly BEFORE the
# val-decl completes, so `x` is never registered as a
# resource-owned local on that path: nothing was ever bound,
# so there is nothing to close/drop.
val try_init = HirExpr(kind: HirExprKind.Try(var_read(code_sym, 10)), has_type_: true, type_: i64_type(), span: mk_span(10))
val let_stmt = HirStmt(kind: HirStmtKind.Let(x_sym, resource_type(res_sym), try_init), span: mk_span(10))
val fn_ = make_fn([code_param], [let_stmt], int_lit(0, 12), 5)
var lowering = MirLowering.new(table)
val fn_result = lowering.lower_function(fn_)
# Nothing to drop on the failed-acquire path...
expect(count_drops_in_block(fn_result, "try_err")).to_equal(0)
# ...but the successful-acquire path registers `x` and owes
# exactly one drop at the function's own eventual exit (no
# close() in this variant).
expect(count_drops(fn_result)).to_equal(1)  # oracle: 1 — named expected value from the requirement
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


## Related Documentation

- **Plan:** `doc/03_plan/language/resource/resource_parallel_agent_plan_2026-08-06.md (WP-K)`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
- `REQ-COMPILER-RESOURCE-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `aa2dc8bda430f40aae6dded90deedef62ab196ecbab09fad65e0e4cab64938d9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `aa2dc8bda430f40aae6dded90deedef62ab196ecbab09fad65e0e4cab64938d9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `aa2dc8bda430f40aae6dded90deedef62ab196ecbab09fad65e0e4cab64938d9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/resource/resource_with_scoped_mir_drop_spec.spl
mirror: doc/06_spec/01_unit/compiler/resource/resource_with_scoped_mir_drop_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/resource/resource_with_scoped_mir_drop_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/resource/resource_with_scoped_mir_drop_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/resource/resource_with_scoped_mir_drop_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/resource/resource_with_scoped_mir_drop_spec.spl:163:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lowers `val x = ACQUIRE; print-ish BODY; x.close()` to exactly one Drop, on the close() site' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/resource/resource_with_scoped_mir_drop_spec.spl:182:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'drops the FRESH with-bound resource before the explicit return, without a param or a move' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/resource/resource_with_scoped_mir_drop_spec.spl:205:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'drops the with-bound resource on the `?` Err path, independent of the acquire' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
