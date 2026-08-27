# Dict / Array Membership Uses a Tagged Key Specification

> Purpose: Prove that Dict membership answers with a tagged key.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dict / Array Membership Uses a Tagged Key Specification

Purpose: Prove that Dict membership answers with a tagged key.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #MIR-MEMBERSHIP-TAGGED-KEY |
| Category | Compiler / codegen runtime ABI |
| Difficulty | 3/5 |
| Status | In Progress |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | doc/08_tracking/bug/dict_array_contains_raw_untagged_key_2026-08-02.md |
| Source | `test/01_unit/compiler/dict_array_membership_tagged_key_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that Dict membership answers with a tagged key.
Audience: COMP maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### Dict membership answers with a tagged key

#### finds every key it stored

- finds every key it stored
- Verify: finds every key it stored


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("finds every key it stored")
step("Verify: finds every key it stored")
# @req: REQ-COMP-DICT-MEMBERSHIP-ANSWERS-WITH-A-TAGGED-KE-001
var b: {i64: i64} = {}
b[7] = 70
b[9] = 90
b[11] = 110
b[13] = 130
assert_true(b.has(7))
assert_true(b.has(9))
assert_true(b.has(11))
assert_true(b.has(13))
```

</details>

#### keeps index reads and keys() consistent with has()

- keeps index reads and keys() consistent with has()
- Verify: keeps index reads and keys() consistent with has()
   - Expected: b[7] equals `70`
   - Expected: b[9] equals `90`
   - Expected: b[11] equals `110`
   - Expected: b[13] equals `130`
   - Expected: b.keys().len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps index reads and keys() consistent with has()")
step("Verify: keeps index reads and keys() consistent with has()")
var b: {i64: i64} = {}
b[7] = 70
b[9] = 90
b[11] = 110
b[13] = 130
expect(b[7]).to_equal(70)
expect(b[9]).to_equal(90)
expect(b[11]).to_equal(110)
expect(b[13]).to_equal(130)
expect(b.keys().len()).to_equal(4)
```

</details>

#### reports absent keys as absent

- reports absent keys as absent
- Verify: reports absent keys as absent


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reports absent keys as absent")
step("Verify: reports absent keys as absent")
var b: {i64: i64} = {}
b[7] = 70
b[9] = 90
b[11] = 110
b[13] = 130
expect_not(b.has(5))
expect_not(b.has(6))
```

</details>

#### answers the in operator in both directions

- answers the in operator in both directions
- Verify: answers the in operator in both directions


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("answers the in operator in both directions")
step("Verify: answers the in operator in both directions")
var b: {i64: i64} = {}
b[7] = 70
b[9] = 90
b[11] = 110
b[13] = 130
assert_true(9 in b)
expect_not(5 in b)
```

</details>

#### finds all 64 keys of a 64-key dict

- finds all 64 keys of a 64-key dict
- Verify: finds all 64 keys of a 64-key dict
   - Expected: missing equals `0`
   - Expected: v.keys().len() equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("finds all 64 keys of a 64-key dict")
step("Verify: finds all 64 keys of a 64-key dict")
var v: {i64: i64} = {}
for i in range(0, 64):
    v[i] = i
var missing = 0
for i in range(0, 64):
    if not v.has(i):
        missing = missing + 1
expect(missing).to_equal(0)
expect(v.keys().len()).to_equal(64)
```

</details>

#### finds both keys of a two-key dict holding 8 and 9

- finds both keys of a two-key dict holding 8 and 9
- Verify: finds both keys of a two-key dict holding 8 and 9


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("finds both keys of a two-key dict holding 8 and 9")
step("Verify: finds both keys of a two-key dict holding 8 and 9")
var w: {i64: i64} = {}
w[8] = 80
w[9] = 90
assert_true(w.has(8))
assert_true(w.has(9))
expect_not(w.has(7))
```

</details>

### Array membership answers with a tagged element

#### finds present elements and rejects absent ones

- finds present elements and rejects absent ones
- Verify: finds present elements and rejects absent ones


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("finds present elements and rejects absent ones")
step("Verify: finds present elements and rejects absent ones")
val a = [10, 9, 30]
assert_true(a.contains(10))
assert_true(a.contains(9))
assert_true(a.contains(30))
expect_not(a.contains(7))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Research:** `doc/08_tracking/bug/dict_array_contains_raw_untagged_key_2026-08-02.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
- `REQ-COMP-DICT-MEMBERSHIP-ANSWERS-WITH-A-TAGGED-KE-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `aa5c69f1d370f3a05d547c1f31dc01c7ce6faaf6f698b6424d4cbe9734b0fcaf`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `aa5c69f1d370f3a05d547c1f31dc01c7ce6faaf6f698b6424d4cbe9734b0fcaf`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `aa5c69f1d370f3a05d547c1f31dc01c7ce6faaf6f698b6424d4cbe9734b0fcaf`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/dict_array_membership_tagged_key_spec.spl
mirror: doc/06_spec/01_unit/compiler/dict_array_membership_tagged_key_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/dict_array_membership_tagged_key_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/dict_array_membership_tagged_key_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/dict_array_membership_tagged_key_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/dict_array_membership_tagged_key_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'finds every key it stored' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/dict_array_membership_tagged_key_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps index reads and keys() consistent with has()' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/dict_array_membership_tagged_key_spec.spl:94:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports absent keys as absent' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
