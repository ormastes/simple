# Class detection: no reserved-keyword-headed expression may reach the flat-AST

> Generalizing spec for

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Class detection: no reserved-keyword-headed expression may reach the flat-AST

Generalizing spec for

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/frontend/flat_bridge_keyword_expr_nillit_class_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Generalizing spec for
`doc/08_tracking/bug/spawn_call_expr_silently_becomes_nillit_2026-07-29.md`.

`spawn(...)` (`EXPR_SPAWN`, tag 39) was one instance of a whole family:
`src/compiler/10.frontend/core/_ParserPrimary/primary_expr.spl` builds
dedicated flat nodes for `await` (`EXPR_AWAIT`, 37), `yield` (`EXPR_YIELD`,
38), `spawn` (`EXPR_SPAWN`, 39) and `do:` (`EXPR_DO_BLOCK`, 44) from ordinary
source text, and `convert_flat_expr` in
`src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl` had a dispatch arm
for **none** of them -- every one fell into the same generic
"unhandled node kind -> `ExprKind.NilLit`" catch-all, discarding the whole
subexpression.

The reproducing spec (`flat_bridge_spawn_call_expr_spec.spl`) pins `spawn`
only. This one pins the CLASS: for each construct, the converted body
statement must NOT be `ExprKind.NilLit`. A future keyword-headed expression
that regains the same defect fails here even if `spawn` keeps working.

## Scenarios

### no keyword-headed expression collapses to NilLit in the flat AST bridge

#### does not collapse `spawn(w)` to NilLit

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- does not collapse `spawn(w)` to NilLit


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not collapse `spawn(w)` to NilLit")
val src = "fn boot(w: i64):\n" +
    "    spawn(w)\n"
val parsed = parse_full_frontend(src, "testdata/fixture_class_spawn.spl", "fixture_class_spawn", Logger(level: 0))
val boot = parsed.functions["boot"]
var collapsed = false
if boot.?:
    val fn_ = boot!
    if fn_.body.stmts.len() > 0:
        match fn_.body.stmts[0].kind:
            case StmtKind.Expr(e):
                match e.kind:
                    case ExprKind.NilLit: collapsed = true
                    case _: collapsed = false
            case _: collapsed = false
assert_false(collapsed)
```

</details>

#### does not collapse `await f()` to NilLit

- does not collapse `await f()` to NilLit


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not collapse `await f()` to NilLit")
val src = "fn f() -> i64:\n" +
    "    1\n" +
    "\n" +
    "fn boot() -> i64:\n" +
    "    await f()\n"
val parsed = parse_full_frontend(src, "testdata/fixture_class_await.spl", "fixture_class_await", Logger(level: 0))
val boot = parsed.functions["boot"]
var collapsed = false
if boot.?:
    val fn_ = boot!
    if fn_.body.stmts.len() > 0:
        match fn_.body.stmts[0].kind:
            case StmtKind.Expr(e):
                match e.kind:
                    case ExprKind.NilLit: collapsed = true
                    case _: collapsed = false
            case _: collapsed = false
assert_false(collapsed)
```

</details>

#### does not collapse `yield 1` to NilLit

- does not collapse `yield 1` to NilLit


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not collapse `yield 1` to NilLit")
val src = "fn boot():\n" +
    "    yield 1\n"
val parsed = parse_full_frontend(src, "testdata/fixture_class_yield.spl", "fixture_class_yield", Logger(level: 0))
val boot = parsed.functions["boot"]
var collapsed = false
if boot.?:
    val fn_ = boot!
    if fn_.body.stmts.len() > 0:
        match fn_.body.stmts[0].kind:
            case StmtKind.Expr(e):
                match e.kind:
                    case ExprKind.NilLit: collapsed = true
                    case _: collapsed = false
            case _: collapsed = false
assert_false(collapsed)
```

</details>

#### keeps an ordinary (non-keyword) call as a Call -- control, must not be NilLit either

- keeps an ordinary (non-keyword) call as a Call -- control, must not be NilLit either


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps an ordinary (non-keyword) call as a Call -- control, must not be NilLit either")
val src = "fn identity(w: i64) -> i64:\n" +
    "    w\n" +
    "\n" +
    "fn boot(w: i64):\n" +
    "    identity(w)\n"
val parsed = parse_full_frontend(src, "testdata/fixture_class_control.spl", "fixture_class_control", Logger(level: 0))
val boot = parsed.functions["boot"]
var label = "missing"
if boot.?:
    val fn_ = boot!
    if fn_.body.stmts.len() > 0:
        match fn_.body.stmts[0].kind:
            case StmtKind.Expr(e):
                match e.kind:
                    case ExprKind.Call(callee, args): label = "Call"
                    case ExprKind.NilLit: label = "NilLit"
                    case _: label = "other"
            case _: label = "other-stmt"
assert_equal(label, "Call")
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

- Canonical SPipe generation for source `cc6e3b52af9b8833842cd867b2021ad6793b523f6a507c882315aadbe00bfc23`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `cc6e3b52af9b8833842cd867b2021ad6793b523f6a507c882315aadbe00bfc23`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `cc6e3b52af9b8833842cd867b2021ad6793b523f6a507c882315aadbe00bfc23`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/frontend/flat_bridge_keyword_expr_nillit_class_spec.spl
mirror: doc/06_spec/01_unit/compiler/frontend/flat_bridge_keyword_expr_nillit_class_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/frontend/flat_bridge_keyword_expr_nillit_class_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/frontend/flat_bridge_keyword_expr_nillit_class_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/frontend/flat_bridge_keyword_expr_nillit_class_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not collapse `spawn(w)` to NilLit' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/frontend/flat_bridge_keyword_expr_nillit_class_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not collapse `await f()` to NilLit' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/frontend/flat_bridge_keyword_expr_nillit_class_spec.spl:80:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not collapse `yield 1` to NilLit' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
