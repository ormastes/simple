# Rt Io File Text Arg Jit Marshalling Specification

> Tests covering rt_io_file_* text arguments must be marshalled as (ptr, len) under the JIT.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Rt Io File Text Arg Jit Marshalling Specification

## Scenarios

### rt_io_file_* text arguments must be marshalled as (ptr, len) under the JIT

#### is not measuring broken infrastructure: the control family works under the JIT

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- is not measuring broken infrastructure: the control family works under the JIT
- Run the family probe under SIMPLE_EXECUTION_MODE=jit
- the independently implemented rt_file_* control family must pass under the JIT


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("is not measuring broken infrastructure: the control family works under the JIT")
step("Run the family probe under SIMPLE_EXECUTION_MODE=jit")
val jit = run_probe(FAMILY_PROBE, "jit")

step("the independently implemented rt_file_* control family must pass under the JIT")
expect(jit).to_contain("PASS control_rt_file_write_text")
expect(jit).to_contain("PASS control_rt_file_exists_true")
expect(jit).to_contain("PASS control_rt_file_read_text")
```

</details>

#### reproduces it: the three text-taking members must work under the JIT

- reproduces it: the three text-taking members must work under the JIT
- Run the family probe under the JIT
- rt_io_file_exists(path) must agree with the control family about a file that demonstrably exists
- rt_io_file_open(path, mode) must hand back a real descriptor, not -1
- rt_io_file_delete(path) must really unlink the file, observed from outside the family


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reproduces it: the three text-taking members must work under the JIT")
step("Run the family probe under the JIT")
val jit = run_probe(FAMILY_PROBE, "jit")

step("rt_io_file_exists(path) must agree with the control family about a file that demonstrably exists")
expect(jit).to_contain("PASS rt_io_file_exists_agrees_with_control")

step("rt_io_file_open(path, mode) must hand back a real descriptor, not -1")
expect(jit).to_contain("PASS rt_io_file_open_returns_nonnegative_fd")

step("rt_io_file_delete(path) must really unlink the file, observed from outside the family")
expect(jit).to_contain("PASS rt_io_file_delete_really_removes_file")
```

</details>

#### discriminates: the fd-taking members are ALREADY correct under the JIT, so the defect is the text argument

- discriminates: the fd-taking members are ALREADY correct under the JIT, so the defect is the text argument
- Run the fd-only probe, whose descriptor comes from the control family, under the JIT
- seek/meta/flush/close take only i64 — no text expansion is involved and they must pass


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("discriminates: the fd-taking members are ALREADY correct under the JIT, so the defect is the text argument")
step("Run the fd-only probe, whose descriptor comes from the control family, under the JIT")
val jit = run_probe(FD_PROBE, "jit")

step("seek/meta/flush/close take only i64 — no text expansion is involved and they must pass")
expect(jit).to_contain("PASS meta_size_is_ten")
expect(jit).to_contain("PASS seek_end_minus_1")
expect(jit).to_contain("PASS close_ok")
expect(jit).to_contain("RT_IO_FILE FD PROBE: ALL PASS")
```

</details>

#### keeps the interpreter arm honest: the same family is correct there and must stay correct

- keeps the interpreter arm honest: the same family is correct there and must stay correct
- Run the family probe under SIMPLE_EXECUTION_MODE=interpreter
- interpret mode dispatches through interpreter_extern/io_file.rs and never touches the text-arg table


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps the interpreter arm honest: the same family is correct there and must stay correct")
step("Run the family probe under SIMPLE_EXECUTION_MODE=interpreter")
val interp = run_probe(FAMILY_PROBE, "interpreter")

step("interpret mode dispatches through interpreter_extern/io_file.rs and never touches the text-arg table")
expect(interp).to_contain("RT_IO_FILE PROBE: ALL PASS")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/io/rt_io_file_text_arg_jit_marshalling_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering rt_io_file_* text arguments must be marshalled as (ptr, len) under the JIT.
- rt_io_file_* text arguments must be marshalled as (ptr, len) under the JIT

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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `fafeb3a9909f0adafc85ec79a1966d4774a1676a26047a96eca0846db90856fc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fafeb3a9909f0adafc85ec79a1966d4774a1676a26047a96eca0846db90856fc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fafeb3a9909f0adafc85ec79a1966d4774a1676a26047a96eca0846db90856fc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/io/rt_io_file_text_arg_jit_marshalling_spec.spl
mirror: doc/06_spec/01_unit/lib/io/rt_io_file_text_arg_jit_marshalling_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/io/rt_io_file_text_arg_jit_marshalling_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/io/rt_io_file_text_arg_jit_marshalling_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/io/rt_io_file_text_arg_jit_marshalling_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is not measuring broken infrastructure: the control family works under the JIT' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/io/rt_io_file_text_arg_jit_marshalling_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reproduces it: the three text-taking members must work under the JIT' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/io/rt_io_file_text_arg_jit_marshalling_spec.spl:86:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'discriminates: the fd-taking members are ALREADY correct under the JIT, so the defect is the text argument' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
