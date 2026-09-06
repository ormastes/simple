# `resource` MIR-interpreter drop parity -- WP-I acceptance

> SAME `MirLowering` every backend shares (implicit scope end, explicit

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# `resource` MIR-interpreter drop parity -- WP-I acceptance

SAME `MirLowering` every backend shares (implicit scope end, explicit

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Plan | doc/03_plan/language/resource/resource_parallel_agent_plan_2026-08-06.md (WP-I) |
| Source | `test/01_unit/compiler/resource/resource_interp_drop_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

**Depends on:** WP-E (`794bbf6642f`) -- new `MirInstKind.Drop`, emitted by the
SAME `MirLowering` every backend shares (implicit scope end, explicit
`return`, `?` Err/None early-return, and `.close()` as a consuming drop).

Because drop TIMING is produced by `MirLowering` itself (not by any backend),
`SIMPLE_EXECUTION_MODE=interpreter` running `resource_mir_drop_spec.spl`
(WP-E's own spec, which drives `MirLowering.lower_function` directly and
never executes a function) already proves timing parity by construction --
there is only one lowering implementation to diverge from. What that spec
CANNOT prove is that the MIR interpreter (`compiler.interp.mir_interpreter`,
used by the interpreter backend, `src/compiler/70.backend/backend/interpreter.spl`)
can actually EXECUTE a function containing the `Drop` instructions WP-E now
emits. Before this change it could not: `MirInterpreter.execute_instruction`
had no `Drop` arm and fell through to `case _:`, returning
`InterpError.UnsupportedOperation("unknown instruction")` -- so ANY
resource-typed local, or any `.close()` call, made the containing function
uninterpretable. This spec is the sabotage-able oracle for that gap.

## Scenarios

### WP-I: MIR interpreter executes MirInstKind.Drop directly

#### treats a bare Drop instruction as a no-op, not an unsupported operation

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- treats a bare Drop instruction as a no-op, not an unsupported operation


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("treats a bare Drop instruction as a no-op, not an unsupported operation")
var interp = MirInterpreter.create()
val err = interp.execute_instruction(drop_local_inst(1))
expect(err).to_be_nil()
```

</details>

### WP-I: MIR interpreter executes a lowered resource-param function containing Drop

#### runs a function with an owned resource param (implicit scope-end drop) to completion

- runs a function with an owned resource param (implicit scope-end drop) to completion
   - Expected: ret.unwrap() equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("runs a function with an owned resource param (implicit scope-end drop) to completion")
val (table, res_sym) = setup()
val fn_ = make_fn([resource_param(SymbolId(id: 1), res_sym)], [], int_lit(42, 10), 5)
var lowering = MirLowering.new(table)
val fn_result = lowering.lower_function(fn_)

var interp = MirInterpreter.create()
val (ret, err) = interp.execute_function(fn_result)
expect(err).to_be_nil()
expect(ret.unwrap()).to_equal(42)
```

</details>

#### runs a function whose `.close()` lowers to a consuming Drop to completion

- runs a function whose `.close()` lowers to a consuming Drop to completion
   - Expected: ret.unwrap() equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("runs a function whose `.close()` lowers to a consuming Drop to completion")
val (table, res_sym) = setup()
val a_sym = SymbolId(id: 1)
val close_stmt = HirStmt(kind: HirStmtKind.Expr(HirExpr(kind: HirExprKind.MethodCall(var_read(a_sym, 10), "close", [], MethodResolution.Unresolved), has_type_: false, type_: i64_type(), span: mk_span(10))), span: mk_span(10))
val fn_ = make_fn([resource_param(a_sym, res_sym)], [close_stmt], int_lit(7, 12), 5)
var lowering = MirLowering.new(table)
val fn_result = lowering.lower_function(fn_)

var interp = MirInterpreter.create()
val (ret, err) = interp.execute_function(fn_result)
expect(err).to_be_nil()
expect(ret.unwrap()).to_equal(7)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/language/resource/resource_parallel_agent_plan_2026-08-06.md (WP-I)`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `fcf81e1545c6e1fafa468b69162d813f2e3a4f6b45f2f7081e575fb39f9583f1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fcf81e1545c6e1fafa468b69162d813f2e3a4f6b45f2f7081e575fb39f9583f1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fcf81e1545c6e1fafa468b69162d813f2e3a4f6b45f2f7081e575fb39f9583f1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/compiler/resource/resource_interp_drop_spec.spl
mirror: doc/06_spec/01_unit/compiler/resource/resource_interp_drop_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/resource/resource_interp_drop_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/resource/resource_interp_drop_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/resource/resource_interp_drop_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/resource/resource_interp_drop_spec.spl:112:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'treats a bare Drop instruction as a no-op, not an unsupported operation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/resource/resource_interp_drop_spec.spl:120:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'runs a function with an owned resource param (implicit scope-end drop) to completion' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/resource/resource_interp_drop_spec.spl:133:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'runs a function whose `.close()` lowers to a consuming Drop to completion' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
