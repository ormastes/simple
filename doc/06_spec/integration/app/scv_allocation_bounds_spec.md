# scv_allocation_bounds_spec

> Purpose: This spec proves SCV's MCI-v2 allocation bounds reject oversize

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# scv_allocation_bounds_spec

Purpose: This spec proves SCV's MCI-v2 allocation bounds reject oversize

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/integration/app/scv_allocation_bounds_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves SCV's MCI-v2 allocation bounds reject oversize
objects, trees, over-depth deltas and oversize parser input with a named error
while leaving the store byte-for-byte unchanged and integrity-clean.
Audience: Maintainers of SCV and of the mission-critical hardening v2 lanes.

## Scenarios

### scv allocation bounds

#### rejects an oversize pack object before materialising it

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects an oversize pack object before materialising it
- declare a v2 pack entry one byte over SCV_MAX_OBJECT_BYTES
- resolve the entry: named bound error, no bytes copied
   - Expected: data.len() equals `0`
   - Expected: scv_bound_object_bytes(SCV_MAX_OBJECT_BYTES) equals ``
- store is unchanged and fsck stays clean


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects an oversize pack object before materialising it")
step("declare a v2 pack entry one byte over SCV_MAX_OBJECT_BYTES")
val root = _fresh_repo("object")
val before = _store_fingerprint(root)
val fsck_before = scv_fsck(root)
val oversize = SCV_MAX_OBJECT_BYTES + 1
val payload = "format: scv-pack-payload-v2\nentry chunks chunk_big {oversize}\n".bytes()
step("resolve the entry: named bound error, no bytes copied")
val (data, err) = scv_pack_resolve_object(payload, "chunk_big")
expect(err).to_contain(BOUND_ERROR)
expect(err).to_contain("object bytes requested {oversize}, bound {SCV_MAX_OBJECT_BYTES}")
expect(data.len()).to_equal(0)
expect(scv_bound_object_bytes(SCV_MAX_OBJECT_BYTES)).to_equal("")
step("store is unchanged and fsck stays clean")
_expect_store_intact(root, before, fsck_before)
```

</details>

#### rejects an oversize tree entry count

- rejects an oversize tree entry count
- charge one entry over SCV_MAX_TREE_ENTRIES against the arena
   - Expected: scv_bound_tree_entries(SCV_MAX_TREE_ENTRIES) equals ``
- store is unchanged and fsck stays clean


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects an oversize tree entry count")
step("charge one entry over SCV_MAX_TREE_ENTRIES against the arena")
val root = _fresh_repo("tree")
val before = _store_fingerprint(root)
val fsck_before = scv_fsck(root)
val err = scv_bound_tree_entries(SCV_MAX_TREE_ENTRIES + 1)
expect(err).to_contain(BOUND_ERROR)
expect(err).to_contain("tree entries requested {SCV_MAX_TREE_ENTRIES + 1}, bound {SCV_MAX_TREE_ENTRIES}")
expect(scv_bound_tree_entries(SCV_MAX_TREE_ENTRIES)).to_equal("")
step("store is unchanged and fsck stays clean")
_expect_store_intact(root, before, fsck_before)
```

</details>

#### rejects an over-depth delta chain and an oversize delta target

- rejects an over-depth delta chain and an oversize delta target
- verify a v2 payload whose chain depth exceeds SCV_DELTA_MAX_DEPTH
- decode a delta whose declared target size exceeds SCV_MAX_DELTA_TARGET_BYTES
   - Expected: out.len() equals `0`
   - Expected: scv_bound_delta_target_bytes(SCV_MAX_DELTA_TARGET_BYTES) equals ``
- store is unchanged and fsck stays clean


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects an over-depth delta chain and an oversize delta target")
step("verify a v2 payload whose chain depth exceeds SCV_DELTA_MAX_DEPTH")
val root = _fresh_repo("delta")
val before = _store_fingerprint(root)
val fsck_before = scv_fsck(root)
val depth = SCV_DELTA_MAX_DEPTH + 1
val chain = "format: scv-pack-payload-v2\nentry chunks base_1 4\nbase\nendentry\nentry-delta chunks d_1 base_1 {depth} 4\nxxxx\nendentry\n".bytes()
expect(scv_pack_v2_verify_payload(chain)).to_contain("ERROR chain depth {depth} exceeds maximum {SCV_DELTA_MAX_DEPTH}")
step("decode a delta whose declared target size exceeds SCV_MAX_DELTA_TARGET_BYTES")
val oversize = SCV_MAX_DELTA_TARGET_BYTES + 1
var delta: [u8] = [68u8, 69u8, 76u8, 84u8]
for b in _u32_le(0):
    delta.push(b)
for b in _u32_le(oversize):
    delta.push(b)
for b in _u32_le(0):
    delta.push(b)
val (out, err) = scv_delta_decode([], delta)
expect(err).to_contain(BOUND_ERROR)
expect(err).to_contain("delta target bytes requested {oversize}, bound {SCV_MAX_DELTA_TARGET_BYTES}")
expect(out.len()).to_equal(0)
expect(scv_bound_delta_target_bytes(SCV_MAX_DELTA_TARGET_BYTES)).to_equal("")
step("store is unchanged and fsck stays clean")
_expect_store_intact(root, before, fsck_before)
```

</details>

#### rejects oversize parser input before reading it

- rejects oversize parser input before reading it
- create a sparse file one byte over SCV_MAX_PARSER_INPUT_BYTES
- parse it: named bound error, no parser artifacts written
   - Expected: scv_bound_parser_input_bytes(SCV_MAX_PARSER_INPUT_BYTES) equals ``
- store is unchanged and fsck stays clean


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects oversize parser input before reading it")
step("create a sparse file one byte over SCV_MAX_PARSER_INPUT_BYTES")
val root = _fresh_repo("parser")
val before = _store_fingerprint(root)
val fsck_before = scv_fsck(root)
val oversize = SCV_MAX_PARSER_INPUT_BYTES + 1
_sh("truncate -s {oversize} '{root}/big.txt'")
step("parse it: named bound error, no parser artifacts written")
val err = scv_parse_file(root, "{root}/big.txt")
expect(err).to_contain(BOUND_ERROR)
expect(err).to_contain("parser input bytes requested {oversize}, bound {SCV_MAX_PARSER_INPUT_BYTES}")
expect(scv_bound_parser_input_bytes(SCV_MAX_PARSER_INPUT_BYTES)).to_equal("")
step("store is unchanged and fsck stays clean")
_expect_store_intact(root, before, fsck_before)
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

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `79a377ed7aebd4ad4456fd6cb73342367285f7578e4f618862f1128fd69c7afa`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `79a377ed7aebd4ad4456fd6cb73342367285f7578e4f618862f1128fd69c7afa`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `79a377ed7aebd4ad4456fd6cb73342367285f7578e4f618862f1128fd69c7afa`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/integration/app/scv_allocation_bounds_spec.spl
mirror: doc/06_spec/integration/app/scv_allocation_bounds_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/app/scv_allocation_bounds_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/app/scv_allocation_bounds_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/app/scv_allocation_bounds_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/app/scv_allocation_bounds_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects an oversize pack object before materialising it' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_allocation_bounds_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects an oversize tree entry count' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_allocation_bounds_spec.spl:91:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects an over-depth delta chain and an oversize delta target' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
