# checkpoint_spec

> Purpose: Prove that Checkpoint struct.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# checkpoint_spec

Purpose: Prove that Checkpoint struct.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/test_runner_new/checkpoint_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that Checkpoint struct.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### Checkpoint struct

#### should create checkpoint with all fields

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should create checkpoint with all fields
- Verify: should create checkpoint with all fields
   - Expected: ckpt.timestamp_ms equals `1739530800000`
   - Expected: ckpt.completed_files.len() equals `2`
   - Expected: ckpt.total_passed equals `10`
   - Expected: ckpt.total_failed equals `2`
   - Expected: ckpt.total_skipped equals `3`
   - Expected: ckpt.shutdown_reason equals `memory`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should create checkpoint with all fields")
step("Verify: should create checkpoint with all fields")
# @req: REQ-APP-TEST-RUNNER-NEW-001
val ckpt = TestCheckpoint(
    timestamp_ms: 1739530800000,
    completed_files: ["test1.spl", "test2.spl"],
    total_passed: 10,
    total_failed: 2,
    total_skipped: 3,
    shutdown_reason: "memory"
)

expect(ckpt.timestamp_ms).to_equal(1739530800000)  # oracle: 1739530800000 — named expected value from the requirement
expect(ckpt.completed_files.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(ckpt.total_passed).to_equal(10)  # oracle: 10 — named expected value from the requirement
expect(ckpt.total_failed).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(ckpt.total_skipped).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(ckpt.shutdown_reason).to_equal("memory")
```

</details>

### make_empty_checkpoint

#### should create empty checkpoint

- should create empty checkpoint
- Verify: should create empty checkpoint
   - Expected: ckpt.timestamp_ms equals `0`
   - Expected: ckpt.completed_files.len() equals `0`
   - Expected: ckpt.total_passed equals `0`
   - Expected: ckpt.total_failed equals `0`
   - Expected: ckpt.total_skipped equals `0`
   - Expected: ckpt.shutdown_reason equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should create empty checkpoint")
step("Verify: should create empty checkpoint")
val ckpt = make_empty_checkpoint()

expect(ckpt.timestamp_ms).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(ckpt.completed_files.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(ckpt.total_passed).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(ckpt.total_failed).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(ckpt.total_skipped).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(ckpt.shutdown_reason).to_equal("")
```

</details>

### checkpoint_save and load

#### should save checkpoint to file

- should save checkpoint to file
- Verify: should save checkpoint to file
   - Expected: exists is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should save checkpoint to file")
step("Verify: should save checkpoint to file")
val completed = ["test/unit/a.spl", "test/unit/b.spl"]
checkpoint_save(completed, 5, 1, 2, "cpu")

val exists = file_exists(".simple-test-checkpoint.sdn")
expect(exists).to_equal(true)
```

</details>

#### should save valid SDN format

- should save valid SDN format
- Verify: should save valid SDN format
   - Expected: content contains `checkpoint {`
   - Expected: content contains `timestamp_ms`
   - Expected: content contains `completed_files`
   - Expected: content contains `total_passed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should save valid SDN format")
step("Verify: should save valid SDN format")
val completed = ["file1.spl"]
checkpoint_save(completed, 10, 0, 0, "periodic")

val content = file_read(".simple-test-checkpoint.sdn")

# Check for expected SDN structure
expect(content.contains("checkpoint {")).to_equal(true)
expect(content.contains("timestamp_ms")).to_equal(true)
expect(content.contains("completed_files")).to_equal(true)
expect(content.contains("total_passed")).to_equal(true)
```

</details>

#### should load saved checkpoint

- should load saved checkpoint
- Verify: should load saved checkpoint
   - Expected: loaded.completed_files.len() equals `2`
   - Expected: loaded.completed_files[0] equals `test/unit/x.spl`
   - Expected: loaded.completed_files[1] equals `test/unit/y.spl`
   - Expected: loaded.total_passed equals `15`
   - Expected: loaded.total_failed equals `3`
   - Expected: loaded.total_skipped equals `5`
   - Expected: loaded.shutdown_reason equals `memory`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should load saved checkpoint")
step("Verify: should load saved checkpoint")
val completed = ["test/unit/x.spl", "test/unit/y.spl"]
checkpoint_save(completed, 15, 3, 5, "memory")

val loaded = checkpoint_load()

expect(loaded.completed_files.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(loaded.completed_files[0]).to_equal("test/unit/x.spl")
expect(loaded.completed_files[1]).to_equal("test/unit/y.spl")
expect(loaded.total_passed).to_equal(15)  # oracle: 15 — named expected value from the requirement
expect(loaded.total_failed).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(loaded.total_skipped).to_equal(5)  # oracle: 5 — named expected value from the requirement
expect(loaded.shutdown_reason).to_equal("memory")
```

</details>

### checkpoint_skip_completed

#### should return all files when checkpoint empty

- should return all files when checkpoint empty
- Verify: should return all files when checkpoint empty
   - Expected: remaining.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should return all files when checkpoint empty")
step("Verify: should return all files when checkpoint empty")
val all_files = ["a.spl", "b.spl", "c.spl"]
val ckpt = make_empty_checkpoint()

val remaining = checkpoint_skip_completed(all_files, ckpt)

expect(remaining.len()).to_equal(3)  # oracle: 3 — named expected value from the requirement
```

</details>

#### should filter out completed files

- should filter out completed files
- Verify: should filter out completed files
   - Expected: remaining.len() equals `2`
   - Expected: remaining[0] equals `test/b.spl`
   - Expected: remaining[1] equals `test/d.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should filter out completed files")
step("Verify: should filter out completed files")
val all_files = ["test/a.spl", "test/b.spl", "test/c.spl", "test/d.spl"]
val ckpt = TestCheckpoint(
    timestamp_ms: 0,
    completed_files: ["test/a.spl", "test/c.spl"],
    total_passed: 0,
    total_failed: 0,
    total_skipped: 0,
    shutdown_reason: ""
)

val remaining = checkpoint_skip_completed(all_files, ckpt)

expect(remaining.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(remaining[0]).to_equal("test/b.spl")
expect(remaining[1]).to_equal("test/d.spl")
```

</details>

#### should return empty when all completed

- should return empty when all completed
- Verify: should return empty when all completed
   - Expected: remaining.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should return empty when all completed")
step("Verify: should return empty when all completed")
val all_files = ["x.spl", "y.spl"]
val ckpt = TestCheckpoint(
    timestamp_ms: 0,
    completed_files: ["x.spl", "y.spl"],
    total_passed: 0,
    total_failed: 0,
    total_skipped: 0,
    shutdown_reason: ""
)

val remaining = checkpoint_skip_completed(all_files, ckpt)

expect(remaining.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-APP-TEST-RUNNER-NEW-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d86663a7b99bcc72bdecb00464c6dd08a5ca29d7467daab566ff1b5fc1138adf`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d86663a7b99bcc72bdecb00464c6dd08a5ca29d7467daab566ff1b5fc1138adf`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d86663a7b99bcc72bdecb00464c6dd08a5ca29d7467daab566ff1b5fc1138adf`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/app/test_runner_new/checkpoint_spec.spl
mirror: doc/06_spec/unit/app/test_runner_new/checkpoint_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/test_runner_new/checkpoint_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/test_runner_new/checkpoint_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/test_runner_new/checkpoint_spec.spl:25:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should create checkpoint with all fields' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/app/test_runner_new/checkpoint_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should create checkpoint with all fields' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/test_runner_new/checkpoint_spec.spl:47:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should create empty checkpoint' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/app/test_runner_new/checkpoint_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should create empty checkpoint' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/test_runner_new/checkpoint_spec.spl:66:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should save checkpoint to file' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/app/test_runner_new/checkpoint_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should save checkpoint to file' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/test_runner_new/checkpoint_spec.spl:76:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should save valid SDN format' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/app/test_runner_new/checkpoint_spec.spl:91:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should load saved checkpoint' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/app/test_runner_new/checkpoint_spec.spl:109:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should return all files when checkpoint empty' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
