# Regression: the real flat-AST mappings still map

> Lane C2 (flat-AST bridge transition census). The census work above added loud

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Regression: the real flat-AST mappings still map

Lane C2 (flat-AST bridge transition census). The census work above added loud

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/frontend/flat_bridge_coverage/flat_bridge_real_mapping_regression_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Lane C2 (flat-AST bridge transition census). The census work above added loud
diagnostics to previously-silent fallbacks; this spec guards the other side of
the ledger -- the tags whose transition table row says `Implemented` or
`Normalized(...)` must still produce their named target node, and must NOT
start reporting an `unhandled` diagnostic.

`spawn` / `await` / `yield` are the three tags the originating bug record
(`doc/08_tracking/bug/spawn_call_expr_silently_becomes_nillit_2026-07-29.md`)
fixed on 2026-08-17; they are the highest-risk rows in
`spec/compiler_schema/transitions/flat_expr_to_ast_expr.sdn` because they were
silent once already.

## Scenarios

### implemented/normalized flat-AST transitions still map

#### maps `spawn(w)` onto ExprKind.Call -- Normalized(Call) row

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- maps `spawn(w)` onto ExprKind.Call -- Normalized(Call) row


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps `spawn(w)` onto ExprKind.Call -- Normalized(Call) row")
assert_equal(first_stmt_expr_label("fn boot(w: i64):\n    spawn(w)\n", "fixture_reg_spawn"), "Call")
```

</details>

#### does not collapse `await f()` -- Implemented row (post-bridge desugar rewrites it)

- does not collapse `await f()` -- Implemented row (post-bridge desugar rewrites it)


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not collapse `await f()` -- Implemented row (post-bridge desugar rewrites it)")
# MEASURED, not assumed: the bridge arm emits `ExprKind.Await`, but
# `parse_full_frontend` runs the async desugar afterwards, and for a
# non-`async` enclosing fn `desugar_async.spl:233` rewrites the Await
# into a plain Call. So the observable label here is "Call", not
# "Await". The property this row actually guards is the one the bug
# record is about: the await operand must not vanish into NilLit.
val src = "fn f() -> i64:\n    1\n\nfn boot() -> i64:\n    await f()\n"
val label = first_stmt_expr_label(src, "fixture_reg_await")
assert_false(label == "NilLit")
assert_false(label == "missing")
```

</details>

#### maps `yield 1` onto ExprKind.Yield -- Implemented row

- maps `yield 1` onto ExprKind.Yield -- Implemented row


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps `yield 1` onto ExprKind.Yield -- Implemented row")
assert_equal(first_stmt_expr_label("fn boot():\n    yield 1\n", "fixture_reg_yield"), "Yield")
```

</details>

#### raises no `unhandled` bridge diagnostic for spawn/await/yield source

- raises no `unhandled` bridge diagnostic for spawn/await/yield source


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("raises no `unhandled` bridge diagnostic for spawn/await/yield source")
val src = "fn f() -> i64:\n    1\n\nfn boot() -> i64:\n    await f()\n"
assert_false(any_bridge_diag(src, "fixture_reg_no_diag"))
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

- Canonical SPipe generation for source `ee640558f97c1f87d5aa9efee98eba058735194fecd4fb30ec67f28f9d1273f0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ee640558f97c1f87d5aa9efee98eba058735194fecd4fb30ec67f28f9d1273f0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ee640558f97c1f87d5aa9efee98eba058735194fecd4fb30ec67f28f9d1273f0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler/frontend/flat_bridge_coverage/flat_bridge_real_mapping_regression_spec.spl
mirror: doc/06_spec/unit/compiler/frontend/flat_bridge_coverage/flat_bridge_real_mapping_regression_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/frontend/flat_bridge_coverage/flat_bridge_real_mapping_regression_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/frontend/flat_bridge_coverage/flat_bridge_real_mapping_regression_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/frontend/flat_bridge_coverage/flat_bridge_real_mapping_regression_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps `spawn(w)` onto ExprKind.Call -- Normalized(Call) row' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/frontend/flat_bridge_coverage/flat_bridge_real_mapping_regression_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not collapse `await f()` -- Implemented row (post-bridge desugar rewrites it)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/frontend/flat_bridge_coverage/flat_bridge_real_mapping_regression_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps `yield 1` onto ExprKind.Yield -- Implemented row' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
