# cuda_intrinsic_arity_table_agrees_with_emitter_spec

> Purpose: Prove that CUDA intrinsic arity table agrees with the emitter.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# cuda_intrinsic_arity_table_agrees_with_emitter_spec

Purpose: Prove that CUDA intrinsic arity table agrees with the emitter.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/cuda_intrinsic_arity_table_agrees_with_emitter_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that CUDA intrinsic arity table agrees with the emitter.
Audience: COMP maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### CUDA intrinsic arity table agrees with the emitter

#### reads the backend source and sees a known binary intrinsic

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reads the backend source and sees a known binary intrinsic
- Verify: reads the backend source and sees a known binary intrinsic
   - Expected: emitter_max_arg_index(source, "gpu_warp_broadcast") equals `1`
   - Expected: table_required_args(source, "gpu_warp_broadcast") equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reads the backend source and sees a known binary intrinsic")
step("Verify: reads the backend source and sees a known binary intrinsic")
# @req: REQ-COMP-CUDA-INTRINSIC-ARITY-TABLE-AGREES-WITH-T-001
val source = read_file_text(CUDA_BACKEND)
expect(source.len()).to_be_greater_than(1000)
# gpu_warp_broadcast genuinely consumes args[0] and args[1] (:1197).
expect(emitter_max_arg_index(source, "gpu_warp_broadcast")).to_equal(1)
expect(table_required_args(source, "gpu_warp_broadcast")).to_equal(2)
```

</details>

#### declares gpu_warp_ballot unary, matching its emitter

- declares gpu_warp_ballot unary, matching its emitter
- Verify: declares gpu_warp_ballot unary, matching its emitter
   - Expected: emitter_max_arg_index(source, "gpu_warp_ballot") equals `0`
   - Expected: table_required_args(source, "gpu_warp_ballot") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("declares gpu_warp_ballot unary, matching its emitter")
step("Verify: declares gpu_warp_ballot unary, matching its emitter")
val source = read_file_text(CUDA_BACKEND)
expect(emitter_max_arg_index(source, "gpu_warp_ballot")).to_equal(0)
expect(table_required_args(source, "gpu_warp_ballot")).to_equal(1)
```

</details>

#### declares gpu_warp_scan_add unary, matching its emitter

- declares gpu_warp_scan_add unary, matching its emitter
- Verify: declares gpu_warp_scan_add unary, matching its emitter
   - Expected: emitter_max_arg_index(source, "gpu_warp_scan_add") equals `0`
   - Expected: table_required_args(source, "gpu_warp_scan_add") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("declares gpu_warp_scan_add unary, matching its emitter")
step("Verify: declares gpu_warp_scan_add unary, matching its emitter")
val source = read_file_text(CUDA_BACKEND)
expect(emitter_max_arg_index(source, "gpu_warp_scan_add")).to_equal(0)
expect(table_required_args(source, "gpu_warp_scan_add")).to_equal(1)
```

</details>

#### keeps every warp intrinsic's table arity equal to its emitter arity

- keeps every warp intrinsic's table arity equal to its emitter arity
- Verify: keeps every warp intrinsic's table arity equal to its emitter arity
   - Expected: mismatches.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps every warp intrinsic's table arity equal to its emitter arity")
step("Verify: keeps every warp intrinsic's table arity equal to its emitter arity")
val source = read_file_text(CUDA_BACKEND)
val names = [
    "gpu_warp_shuffle",
    "gpu_warp_shuffle_down",
    "gpu_warp_shuffle_up",
    "gpu_warp_shuffle_xor",
    "gpu_warp_ballot",
    "gpu_warp_broadcast",
    "gpu_warp_scan_add",
    "gpu_warp_reduce_add"
]
var mismatches: [text] = []
for name in names:
    val emitter_arity = emitter_max_arg_index(source, name) + 1
    val declared = table_required_args(source, name)
    # Only compare when both sides were actually located; a -2/-1 is a
    # parse miss and is reported as its own failure below.
    if emitter_arity > 0 and declared > 0 and emitter_arity != declared:
        mismatches = mismatches + [
            name + " (emitter reads " + emitter_arity.to_text() +
            ", table demands " + declared.to_text() + ")"
        ]
expect(mismatches.len()).to_equal(0)
```

</details>

#### locates both an emitter arm and a table entry for every warp intrinsic

- locates both an emitter arm and a table entry for every warp intrinsic
- Verify: locates both an emitter arm and a table entry for every warp intrinsic
   - Expected: unlocated.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("locates both an emitter arm and a table entry for every warp intrinsic")
step("Verify: locates both an emitter arm and a table entry for every warp intrinsic")
val source = read_file_text(CUDA_BACKEND)
val names = [
    "gpu_warp_shuffle",
    "gpu_warp_shuffle_down",
    "gpu_warp_shuffle_up",
    "gpu_warp_shuffle_xor",
    "gpu_warp_ballot",
    "gpu_warp_broadcast",
    "gpu_warp_scan_add",
    "gpu_warp_reduce_add"
]
var unlocated: [text] = []
for name in names:
    if emitter_max_arg_index(source, name) < -1:
        unlocated = unlocated + [name + " (no emitter arm)"]
    if table_required_args(source, name) < 0:
        unlocated = unlocated + [name + " (no table entry)"]
expect(unlocated.len()).to_equal(0)
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
- `REQ-COMP-CUDA-INTRINSIC-ARITY-TABLE-AGREES-WITH-T-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6c729d18af6f1d20017f0d82a5e6e11b8e67703a72b6056667c6db67d78c1cd1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6c729d18af6f1d20017f0d82a5e6e11b8e67703a72b6056667c6db67d78c1cd1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6c729d18af6f1d20017f0d82a5e6e11b8e67703a72b6056667c6db67d78c1cd1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/backend/cuda_intrinsic_arity_table_agrees_with_emitter_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/cuda_intrinsic_arity_table_agrees_with_emitter_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/backend/cuda_intrinsic_arity_table_agrees_with_emitter_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/backend/cuda_intrinsic_arity_table_agrees_with_emitter_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/backend/cuda_intrinsic_arity_table_agrees_with_emitter_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 8 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/backend/cuda_intrinsic_arity_table_agrees_with_emitter_spec.spl:104:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads the backend source and sees a known binary intrinsic' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/cuda_intrinsic_arity_table_agrees_with_emitter_spec.spl:117:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'declares gpu_warp_ballot unary, matching its emitter' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/cuda_intrinsic_arity_table_agrees_with_emitter_spec.spl:125:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'declares gpu_warp_scan_add unary, matching its emitter' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
