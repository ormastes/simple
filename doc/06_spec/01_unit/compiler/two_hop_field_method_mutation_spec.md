# two_hop_field_method_mutation_spec

> Purpose: Prove that two-hop field-method mutation (cross-module intermediate).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# two_hop_field_method_mutation_spec

Purpose: Prove that two-hop field-method mutation (cross-module intermediate).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/two_hop_field_method_mutation_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that two-hop field-method mutation (cross-module intermediate).
Audience: COMP maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### two-hop field-method mutation (cross-module intermediate)

#### one-hop mutating method persists

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- one-hop mutating method persists
- Verify: one-hop mutating method persists
   - Expected: mid.inner.n equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("one-hop mutating method persists")
step("Verify: one-hop mutating method persists")
# @req: REQ-COMP-TWO-HOP-FIELD-METHOD-MUTATION-CROSS-MODU-001
var mid = TwoHopMid.new()
mid.inner.bump()
expect(mid.inner.n).to_equal(1)
```

</details>

#### two-hop mutating method persists on a var-rooted chain

- two-hop mutating method persists on a var-rooted chain
- Verify: two-hop mutating method persists on a var-rooted chain
   - Expected: root.mid.inner.n equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("two-hop mutating method persists on a var-rooted chain")
step("Verify: two-hop mutating method persists on a var-rooted chain")
var root = TwoHopRoot.new()
root.mid.inner.bump()
expect(root.mid.inner.n).to_equal(1)
```

</details>

#### repeated two-hop mutations accumulate

- repeated two-hop mutations accumulate
- Verify: repeated two-hop mutations accumulate
   - Expected: root.mid.inner.n equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("repeated two-hop mutations accumulate")
step("Verify: repeated two-hop mutations accumulate")
var root = TwoHopRoot.new()
root.mid.inner.bump()
root.mid.inner.bump()
root.mid.inner.bump()
expect(root.mid.inner.n).to_equal(3)
```

</details>

#### two-hop mutating method persists on a self-rooted chain

- two-hop mutating method persists on a self-rooted chain
- Verify: two-hop mutating method persists on a self-rooted chain
   - Expected: svc.count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("two-hop mutating method persists on a self-rooted chain")
step("Verify: two-hop mutating method persists on a self-rooted chain")
val svc = TwoHopService.new()
svc.hit()
svc.hit()
expect(svc.count()).to_equal(2)
```

</details>

#### extract-mutate-write-back workaround stays equivalent

- extract-mutate-write-back workaround stays equivalent
- Verify: extract-mutate-write-back workaround stays equivalent
   - Expected: manual.mid.inner.n equals `direct.mid.inner.n`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("extract-mutate-write-back workaround stays equivalent")
step("Verify: extract-mutate-write-back workaround stays equivalent")
# The workaround shipped in src/os/services/** must remain harmless
# once the direct chain works: both forms must agree.
var direct = TwoHopRoot.new()
direct.mid.inner.bump()

var manual = TwoHopRoot.new()
var mid = manual.mid
mid.inner.bump()
manual.mid = mid

expect(manual.mid.inner.n).to_equal(direct.mid.inner.n)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
- `REQ-COMP-TWO-HOP-FIELD-METHOD-MUTATION-CROSS-MODU-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5efd1ffe97ac75110434c7fc554061bc100cb161bfa629cc354f76019b58a4b6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5efd1ffe97ac75110434c7fc554061bc100cb161bfa629cc354f76019b58a4b6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5efd1ffe97ac75110434c7fc554061bc100cb161bfa629cc354f76019b58a4b6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/two_hop_field_method_mutation_spec.spl
mirror: doc/06_spec/01_unit/compiler/two_hop_field_method_mutation_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/two_hop_field_method_mutation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/two_hop_field_method_mutation_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/two_hop_field_method_mutation_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/two_hop_field_method_mutation_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'one-hop mutating method persists' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/two_hop_field_method_mutation_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'two-hop mutating method persists on a var-rooted chain' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/two_hop_field_method_mutation_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'repeated two-hop mutations accumulate' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
