# contract_retention_spec

> FV2: source contracts survive the canonical pure-Simple parser bridge.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# contract_retention_spec

FV2: source contracts survive the canonical pure-Simple parser bridge.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/frontend/contract_retention_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

FV2: source contracts survive the canonical pure-Simple parser bridge.

## Scenarios

### FV2 source contract retention

#### retains every contract class without executing clauses as body statements

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- retains every contract class without executing clauses as body statements
   - Expected: module.functions contains `guarded`
   - Expected: fn_.contract.preconditions.len() equals `2`
   - Expected: fn_.contract.invariants.len() equals `1`
   - Expected: fn_.contract.postconditions.len() equals `2`
   - Expected: fn_.contract.error_postconditions.len() equals `2`
   - Expected: fn_.contract.postcondition_binding equals `ret`
   - Expected: fn_.contract.error_binding equals `err`
   - Expected: fn_.contract.proof_uses equals `guarded_refinement`
   - Expected: has_decreases is true
   - Expected: fn_.body.stmts.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("retains every contract class without executing clauses as body statements")
val source = "fn guarded(x: i64) -> Result<i64, text>:\n" +
    "    in:\n" +
    "        x >= 0\n" +
    "        x < 100\n" +
    "    invariant:\n" +
    "        x >= 0\n" +
    "    decreases: x\n" +
    "    out(ret):\n" +
    "        ret >= x\n" +
    "        ret < 101\n" +
    "    out_err(err):\n" +
    "        err != \"\"\n" +
    "        err.len() > 0\n" +
    "    proof uses: guarded_refinement\n" +
    "    Ok(x)\n"
val module = parse_and_build_module(source, "fv2_contract_retention.spl")
expect(module.functions.contains("guarded")).to_equal(true)
val fn_ = module.functions["guarded"]
expect(fn_.contract.preconditions.len()).to_equal(2)
expect(fn_.contract.invariants.len()).to_equal(1)
expect(fn_.contract.postconditions.len()).to_equal(2)
expect(fn_.contract.error_postconditions.len()).to_equal(2)
expect(fn_.contract.postcondition_binding).to_equal("ret")
expect(fn_.contract.error_binding).to_equal("err")
expect(fn_.contract.proof_uses).to_equal("guarded_refinement")
expect(fn_.contract.preconditions[0].span.file).to_equal(
    "fv2_contract_retention.spl")
expect(fn_.contract.preconditions[0].span.line).to_be_greater_than(0)
expect(fn_.contract.preconditions[0].span.col).to_be_greater_than(0)
var has_decreases = false
if val _measure = fn_.contract.decrease_measure:
    has_decreases = true
expect(has_decreases).to_equal(true)
expect(fn_.body.stmts.len()).to_equal(1)
```

</details>

#### keeps contract state isolated from adjacent plain functions

- keeps contract state isolated from adjacent plain functions
   - Expected: module.functions contains `identity`
   - Expected: identity.contract.preconditions.len() equals `0`
   - Expected: identity.contract.invariants.len() equals `0`
   - Expected: identity.contract.postconditions.len() equals `0`
   - Expected: identity.contract.error_postconditions.len() equals `0`
   - Expected: identity.contract.postcondition_binding equals ``
   - Expected: identity.contract.error_binding equals ``
   - Expected: identity.contract.proof_uses equals ``
   - Expected: identity_has_decreases is false
   - Expected: identity.body.stmts.len() equals `1`
   - Expected: module.functions contains `fill`
   - Expected: fill.contract.preconditions.len() equals `0`
   - Expected: fill.contract.invariants.len() equals `0`
   - Expected: fill.contract.postconditions.len() equals `0`
   - Expected: fill.contract.error_postconditions.len() equals `0`
   - Expected: fill.contract.postcondition_binding equals ``
   - Expected: fill.contract.error_binding equals ``
   - Expected: fill.contract.proof_uses equals ``
   - Expected: fill_has_decreases is false
   - Expected: fill.body.stmts.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps contract state isolated from adjacent plain functions")
val source = "fn guarded(x: i64) -> i64:\n" +
    "    in:\n" +
    "        x >= 0\n" +
    "    x\n" +
    "fn identity(x: i64) -> i64:\n" +
    "    x\n" +
    "fn fill(out: [i64]) -> i64:\n" +
    "    out.push(1)\n" +
    "    out.len()\n"
val module = parse_and_build_module(source, "fv2_contract_adjacency.spl")
expect(module.functions.contains("identity")).to_equal(true)
val identity = module.functions["identity"]
expect(identity.contract.preconditions.len()).to_equal(0)
expect(identity.contract.invariants.len()).to_equal(0)
expect(identity.contract.postconditions.len()).to_equal(0)
expect(identity.contract.error_postconditions.len()).to_equal(0)
expect(identity.contract.postcondition_binding).to_equal("")
expect(identity.contract.error_binding).to_equal("")
expect(identity.contract.proof_uses).to_equal("")
var identity_has_decreases = false
if val _measure = identity.contract.decrease_measure:
    identity_has_decreases = true
expect(identity_has_decreases).to_equal(false)
expect(identity.body.stmts.len()).to_equal(1)
expect(module.functions.contains("fill")).to_equal(true)
val fill = module.functions["fill"]
expect(fill.contract.preconditions.len()).to_equal(0)
expect(fill.contract.invariants.len()).to_equal(0)
expect(fill.contract.postconditions.len()).to_equal(0)
expect(fill.contract.error_postconditions.len()).to_equal(0)
expect(fill.contract.postcondition_binding).to_equal("")
expect(fill.contract.error_binding).to_equal("")
expect(fill.contract.proof_uses).to_equal("")
var fill_has_decreases = false
if val _measure = fill.contract.decrease_measure:
    fill_has_decreases = true
expect(fill_has_decreases).to_equal(false)
expect(fill.body.stmts.len()).to_equal(2)
```

</details>

#### preserves a typed contract through the parser bridge

- preserves a typed contract through the parser bridge
   - Expected: module.functions contains `sample`
   - Expected: sample.contract.proof_uses equals `sample_refinement`
   - Expected: sample.contract.preconditions.len() equals `0`
   - Expected: sample.body.stmts.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("preserves a typed contract through the parser bridge")
val source = "fn sample(x: i64) -> i64:\n" +
    "    proof uses: sample_refinement\n" +
    "    x\n"
val module = parse_and_build_module(source, "fv2_contract_constructor.spl")
expect(module.functions.contains("sample")).to_equal(true)
val sample = module.functions["sample"]
expect(sample.contract.proof_uses).to_equal("sample_refinement")
expect(sample.contract.preconditions.len()).to_equal(0)
expect(sample.body.stmts.len()).to_equal(1)
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


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `fe2e6851c17202e1f44991cff010c9fc0cd8e0fc2c5ab21a4005be8429be8653`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fe2e6851c17202e1f44991cff010c9fc0cd8e0fc2c5ab21a4005be8429be8653`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fe2e6851c17202e1f44991cff010c9fc0cd8e0fc2c5ab21a4005be8429be8653`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/frontend/contract_retention_spec.spl
mirror: doc/06_spec/01_unit/compiler/frontend/contract_retention_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/frontend/contract_retention_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/frontend/contract_retention_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/frontend/contract_retention_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 17 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/frontend/contract_retention_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'retains every contract class without executing clauses as body statements' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/frontend/contract_retention_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps contract state isolated from adjacent plain functions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/frontend/contract_retention_spec.spl:94:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves a typed contract through the parser bridge' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
