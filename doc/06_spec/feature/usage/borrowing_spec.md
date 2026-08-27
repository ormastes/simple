# borrowing_spec

> Purpose: observe Simple's copy-on-write value semantics through production

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# borrowing_spec

Purpose: observe Simple's copy-on-write value semantics through production

## At a Glance

| Field | Value |
|-------|-------|
| Category | Language Features |
| Status | Active |
| Source | `test/feature/usage/borrowing_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: observe Simple's copy-on-write value semantics through production
stdlib operations (sorted, concatenation, push) instead of literal
self-comparison. Audience: language engineers reasoning about borrowing.

## Scenarios

### Borrowing and Reference Capabilities

#### read-only stdlib operations leave every reader's view unchanged

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- Verify: sorted() returns a new ordering while the source keeps its own
   - Expected: xs.sorted() equals `[1, 2, 3]`
   - Expected: xs equals `[3, 1, 2]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("Verify: sorted() returns a new ordering while the source keeps its own")
val xs = [3, 1, 2]
expect(xs.sorted()).to_equal([1, 2, 3])  # oracle: sorted view is ascending
expect(xs).to_equal([3, 1, 2])  # oracle: source order is preserved for other readers
```

</details>

#### a derived value mutates independently of the original

- Verify: concatenation derives a new value, not a shared buffer
   - Expected: mine + [99] equals `[1, 2, 3, 99]`
   - Expected: mine.len() equals `3`
   - Expected: mine does not contain `99`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("Verify: concatenation derives a new value, not a shared buffer")
val mine = [1, 2, 3]
expect(mine + [99]).to_equal([1, 2, 3, 99])  # oracle: derived copy carries the append
expect(mine.len()).to_equal(3)  # oracle: original length is untouched
expect(mine.contains(99)).to_equal(false)  # oracle: appended element never leaks into the original
```

</details>

#### the single owner mutating in place sees the new state

- Verify: owner-side push is visible through the owning binding
   - Expected: owned.last() equals `4`
   - Expected: owned.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("Verify: owner-side push is visible through the owning binding")
var owned = [1, 2, 3]
owned.push(4)
expect(owned.last()).to_equal(4)  # oracle: pushed element is the new last item
expect(owned.len()).to_equal(4)  # oracle: length grew by exactly one
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

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `fb52b371fcf0b9df6278095db1760fa01a2a0e11b7b1d1317c7c7bb43bb6809f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fb52b371fcf0b9df6278095db1760fa01a2a0e11b7b1d1317c7c7bb43bb6809f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fb52b371fcf0b9df6278095db1760fa01a2a0e11b7b1d1317c7c7bb43bb6809f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/usage/borrowing_spec.spl
mirror: doc/06_spec/feature/usage/borrowing_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/borrowing_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/borrowing_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/borrowing_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'read-only stdlib operations leave every reader's view unchanged' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/borrowing_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'a derived value mutates independently of the original' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/borrowing_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'the single owner mutating in place sees the new state' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
