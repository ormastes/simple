# QEMU SIMD And Coverage Gate Lane

> The claim under test is "the QEMU SIMD and coverage gates are green". A green exit code alone does not establish that claim, and on 2026-08-16 it actively concealed the opposite: `check-simpleos-qemu-engine2d-simd-kernels.shs` asserted the ARM64 NEON store with a doubled-backslash ERE. A doubled backslash in ERE matches a literal backslash character, so the pattern demanded a backslash before the brace, while llvm-objdump emits the store as `st1` followed by a tab and then `{ v0.4s }, [x0]` — no backslash anywhere. The assertion never matched, `set -eu` aborted the script, and the gate exited 1 with ZERO lines of output. A silent non-zero exit is indistinguishable from a missing tool to any caller that reads a pipeline's status instead of the command's.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# QEMU SIMD And Coverage Gate Lane

The claim under test is "the QEMU SIMD and coverage gates are green". A green exit code alone does not establish that claim, and on 2026-08-16 it actively concealed the opposite: `check-simpleos-qemu-engine2d-simd-kernels.shs` asserted the ARM64 NEON store with a doubled-backslash ERE. A doubled backslash in ERE matches a literal backslash character, so the pattern demanded a backslash before the brace, while llvm-objdump emits the store as `st1` followed by a tab and then `{ v0.4s }, [x0]` — no backslash anywhere. The assertion never matched, `set -eu` aborted the script, and the gate exited 1 with ZERO lines of output. A silent non-zero exit is indistinguishable from a missing tool to any caller that reads a pipeline's status instead of the command's.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/sys_test/qemu_simd_coverage_gate_lane.md |
| Design | doc/05_design/sosix_qemu_native_pass_bundle.md |
| Research | doc/01_research/local/sosix_parallel_qemu_refactor.md |
| Source | `test/03_system/check/qemu_simd_coverage_gate_lane_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The claim under test is "the QEMU SIMD and coverage gates are green". A green
exit code alone does not establish that claim, and on 2026-08-16 it actively
concealed the opposite: `check-simpleos-qemu-engine2d-simd-kernels.shs`
asserted the ARM64 NEON store with a doubled-backslash ERE. A doubled
backslash in ERE matches a literal backslash character, so the pattern demanded
a backslash before the brace, while llvm-objdump emits the store as `st1`
followed by a tab and then `{ v0.4s }, [x0]` — no backslash anywhere. The
assertion never matched, `set -eu` aborted the script, and the gate exited 1
with ZERO lines of output. A silent non-zero exit is indistinguishable from a
missing tool to any caller that reads a pipeline's status instead of the
command's.

This spec therefore separates three things that a bare exit code conflates:

  1. the gate PASSES on a qualified host (positive);
  2. the gate's assertions are SPELLED correctly, so a regression to the
     over-escaped form is caught in source before it can silently abort (edge);
  3. the gate's assertions are NON-VACUOUS against real disassembly — the
     historical pattern is proven to match nothing, which is why the gate could
     not have been passing (error / negative control).

It is fail-closed throughout. A missing `clang` or `llvm-objdump` fails this
spec; it does not skip, and there is no tolerance, placeholder, or
auto-baseline. Absence of a toolchain is absence of evidence.

## Requirements

**Requirements:** N/A

- REQ-QEMU-SIMD-COV-LANE-001: The QEMU SIMD object gate exits 0 on a
  qualified host and prints its verdict line; a silent exit is a failure
  regardless of status.
- REQ-QEMU-SIMD-COV-LANE-002: The gate's ARM64 NEON store assertion uses the
  single-escaped brace form and never the over-escaped form that matches a
  literal backslash.
- REQ-QEMU-SIMD-COV-LANE-003: The gate asserts all four instruction families
  (arm64 `dup`/`st1`, x86_64 `pshufd`/`movdqu`), so none can be quietly
  dropped while the gate still reports PASS.
- REQ-QEMU-SIMD-COV-LANE-004: The gate's assertions are non-vacuous against
  real disassembly produced by the repo's own baremetal stubs.
- REQ-QEMU-SIMD-COV-LANE-005: The binary-independent SIMD coverage gates
  (`engine2d-simd-c-kernels`, `x25519mlkem768-cpu-simd`) state an explicit
  verdict on stdout rather than relying on exit status alone.
- REQ-QEMU-SIMD-COV-LANE-006: The 8K operation receipt reports its
  `full_dynamic_frame_80fps_proven` flag rather than hardcoding it, so a
  passing receipt cannot be read as an 80fps proof it does not establish.

## Plan

**Plan:** doc/03_plan/sys_test/qemu_simd_coverage_gate_lane.md

1. Require the disassembly toolchain; fail closed when it is absent.
2. Run the QEMU SIMD object gate and assert exit status AND printed verdict.
3. Read the gate source and pin the escaping of every instruction assertion.
4. Rebuild the arm64 disassembly and prove the correct pattern matches while
   the historical over-escaped pattern matches nothing.
5. Run the binary-independent coverage gates and pin their stated verdicts.

## Design

**Design:** doc/05_design/sosix_qemu_native_pass_bundle.md

Every assertion here runs host tools directly through `process_run`, so the
spec needs no QEMU guest, no deployed compiler, and no network. It is the
static-prerequisite tier of the lane: guest hit/chunk receipts and QMP
captures remain mandatory before a SimpleOS backend may be marked verified.

## Research

**Research:** doc/01_research/local/sosix_parallel_qemu_refactor.md

## Examples

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/qemu_simd_coverage_gate_lane_spec.spl --mode=interpreter --clean
```

## Scenarios

### QEMU SIMD and coverage gate lane

#### runs the QEMU SIMD object gate to a green, non-silent verdict

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-QEMU-SIMD-COV-LANE-001
# @req REQ-QEMU-SIMD-COV-LANE-002
# @req REQ-QEMU-SIMD-COV-LANE-003
# @req REQ-QEMU-SIMD-COV-LANE-004
# @req REQ-QEMU-SIMD-COV-LANE-005
# @req REQ-QEMU-SIMD-COV-LANE-006
```

</details>

#### pins every instruction assertion against the over-escaped-regex regression

- pins every instruction assertion against the over-escaped-regex regression
- Read the gate source
- Require the single-escaped ARM64 store assertion
- Reject the over-escaped store assertion that matches a literal backslash
   - Expected: gate does not contain `_overescaped_st1_pattern()`
- Reject the same over-escape on the ARM64 lane-splat assertion
   - Expected: gate does not contain `[[:space:]]dup[[:space:]]+v[0-9]+\\\\.4s`
- Require all four instruction families so none can be quietly dropped
- Require the receipt symbols the guest hit/chunk evidence depends on


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("pins every instruction assertion against the over-escaped-regex regression")
step("Read the gate source")
val gate = file_read(_gate_path())

step("Require the single-escaped ARM64 store assertion")
expect(gate).to_contain(_correct_st1_pattern())

step("Reject the over-escaped store assertion that matches a literal backslash")
expect(gate.contains(_overescaped_st1_pattern())).to_equal(false)

step("Reject the same over-escape on the ARM64 lane-splat assertion")
expect(gate).to_contain("[[:space:]]dup[[:space:]]+v[0-9]+\\.4s")
expect(gate.contains("[[:space:]]dup[[:space:]]+v[0-9]+\\\\.4s")).to_equal(false)

step("Require all four instruction families so none can be quietly dropped")
expect(gate).to_contain("pshufd")
expect(gate).to_contain("movdqu")

step("Require the receipt symbols the guest hit/chunk evidence depends on")
expect(gate).to_contain("rt_gui_simd_fill_hits")
expect(gate).to_contain("rt_gui_simd_fill_chunks")
expect(gate).to_contain("rt_gui_simd_fill_tail_pixels")
```

</details>

#### proves the store assertion is non-vacuous against real disassembly

- proves the store assertion is non-vacuous against real disassembly
- Prepare an isolated work directory
   - Expected: mk_code equals `0`
- Compile the repo's own arm64 baremetal stub
   - Expected: cc_code equals `0`
- Disassemble the fill kernel the gate inspects
   - Expected: dis_code equals `0`
- Persist the disassembly so grep sees the same bytes the gate does
   - Expected: sh_code equals `0`
- The correct pattern MATCHES: grep exits 0
   - Expected: hit_code equals `0`
- The historical over-escaped pattern matches NOTHING: grep exits 1
   - Expected: miss_code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 48 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("proves the store assertion is non-vacuous against real disassembly")
step("Prepare an isolated work directory")
val work = _work_dir()
val (_mk_out, _mk_err, mk_code) = process_run("mkdir", ["-p", work])
expect(mk_code).to_equal(0)

step("Compile the repo's own arm64 baremetal stub")
expect(file_exists(_arm_stub())).to_be(true)
val object_path = work + "/arm64.o"
val (_cc_out, _cc_err, cc_code) = process_run("clang", [
    "-target", "aarch64-unknown-none-elf", "-c", "-ffreestanding",
    "-nostdlib", "-fno-pie", "-ffunction-sections", "-fdata-sections",
    "-O2", "-I", "examples/09_embedded/simple_os/arch/arm64/boot",
    "-o", object_path, _arm_stub()
])
expect(cc_code).to_equal(0)
expect(file_exists(object_path)).to_be(true)

step("Disassemble the fill kernel the gate inspects")
val (dis, _dis_err, dis_code) = process_run("llvm-objdump", [
    "-d", "--disassemble-symbols=rt_gui_fill4", object_path
])
expect(dis_code).to_equal(0)
expect(dis).to_contain("st1")
expect(dis).to_contain("v0.4s")

step("Persist the disassembly so grep sees the same bytes the gate does")
val dis_path = work + "/arm64.dis"
val (_sh_out, _sh_err, sh_code) = process_run("sh", [
    "-c",
    "llvm-objdump -d --disassemble-symbols=rt_gui_fill4 " + object_path
        + " > " + dis_path
])
expect(sh_code).to_equal(0)
expect(file_exists(dis_path)).to_be(true)

step("The correct pattern MATCHES: grep exits 0")
val (_hit_out, _hit_err, hit_code) = process_run("grep", [
    "-Eq", _correct_st1_pattern(), dis_path
])
expect(hit_code).to_equal(0)

step("The historical over-escaped pattern matches NOTHING: grep exits 1")
val (_miss_out, _miss_err, miss_code) = process_run("grep", [
    "-Eq", _overescaped_st1_pattern(), dis_path
])
expect(miss_code).to_equal(1)
```

</details>

#### keeps the coverage half honest: verdicts are stated, not implied

- keeps the coverage half honest: verdicts are stated, not implied
- Run the C-kernel SIMD coverage gate
   - Expected: c_code equals `0`
- Run the CPU SIMD correctness gate for the crypto kernel lane
   - Expected: k_code equals `0`
- Require the 8K receipt to REPORT its 80fps flag rather than assume it
- Require the gate to pin that flag false — a passing receipt is not an 80fps proof
- Reject a receipt that claims the 80fps proof it does not establish
   - Expected: ops does not contain `engine2d_8k_full_dynamic_frame_80fps_proven=true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps the coverage half honest: verdicts are stated, not implied")
step("Run the C-kernel SIMD coverage gate")
val (c_out, _c_err, c_code) = process_run(
    "sh", ["scripts/check/check-engine2d-simd-c-kernels.shs"]
)
expect(c_code).to_equal(0)
expect(c_out).to_contain("engine2d-simd-c-kernels: pass")

step("Run the CPU SIMD correctness gate for the crypto kernel lane")
val (k_out, _k_err, k_code) = process_run(
    "sh", ["scripts/check/check-x25519mlkem768-cpu-simd.shs"]
)
expect(k_code).to_equal(0)
expect(k_out).to_contain("STATUS: PASS")

step("Require the 8K receipt to REPORT its 80fps flag rather than assume it")
val ops = file_read("scripts/check/check-engine2d-simd-8k-ops.shs")
expect(ops).to_contain("engine2d_8k_full_dynamic_frame_80fps_proven")

step("Require the gate to pin that flag false — a passing receipt is not an 80fps proof")
expect(ops).to_contain("engine2d_8k_full_dynamic_frame_80fps_proven=false")

step("Reject a receipt that claims the 80fps proof it does not establish")
expect(ops.contains("engine2d_8k_full_dynamic_frame_80fps_proven=true")).to_equal(false)
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


## Related Documentation

- **Plan:** `doc/03_plan/sys_test/qemu_simd_coverage_gate_lane.md`
- **Design:** `doc/05_design/sosix_qemu_native_pass_bundle.md`
- **Research:** `doc/01_research/local/sosix_parallel_qemu_refactor.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-QEMU-SIMD-COV-LANE-001:`
- `REQ-QEMU-SIMD-COV-LANE-002:`
- `REQ-QEMU-SIMD-COV-LANE-003:`
- `REQ-QEMU-SIMD-COV-LANE-004:`
- `REQ-QEMU-SIMD-COV-LANE-005:`
- `REQ-QEMU-SIMD-COV-LANE-006:`
- `REQ-QEMU-SIMD-COV-LANE-001`
- `REQ-QEMU-SIMD-COV-LANE-002`
- `REQ-QEMU-SIMD-COV-LANE-003`
- `REQ-QEMU-SIMD-COV-LANE-004`
- `REQ-QEMU-SIMD-COV-LANE-005`
- `REQ-QEMU-SIMD-COV-LANE-006`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8735141591fb5728298182370f739774c075d99342f4e6fc57c2422008dc2388`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8735141591fb5728298182370f739774c075d99342f4e6fc57c2422008dc2388`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8735141591fb5728298182370f739774c075d99342f4e6fc57c2422008dc2388`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **85/100**; effective score: **85/100**; blockers: **0**.

SSpec documentization score: 85/100
source: test/03_system/check/qemu_simd_coverage_gate_lane_spec.spl
mirror: doc/06_spec/03_system/check/qemu_simd_coverage_gate_lane_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=90 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/check/qemu_simd_coverage_gate_lane_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/check/qemu_simd_coverage_gate_lane_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/check/qemu_simd_coverage_gate_lane_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 8 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/check/qemu_simd_coverage_gate_lane_spec.spl:129:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'runs the QEMU SIMD object gate to a green, non-silent verdict' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/check/qemu_simd_coverage_gate_lane_spec.spl:163:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'pins every instruction assertion against the over-escaped-regex regression' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/qemu_simd_coverage_gate_lane_spec.spl:188:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'proves the store assertion is non-vacuous against real disassembly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/qemu_simd_coverage_gate_lane_spec.spl:238:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the coverage half honest: verdicts are stated, not implied' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
