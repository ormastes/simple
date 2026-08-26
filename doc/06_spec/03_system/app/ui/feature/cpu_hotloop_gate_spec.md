# Cpu Hotloop Gate Specification

> Tests covering CPU-lane hot-loop enforcement gate (design §6.1 / plan W2).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cpu Hotloop Gate Specification

## Scenarios

### CPU-lane hot-loop enforcement gate (design §6.1 / plan W2)

#### has a gate script

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- has a gate script
   - Expected: file_exists("scripts/check/check-cpu-hotloop-idiom.shs") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has a gate script")
expect(file_exists("scripts/check/check-cpu-hotloop-idiom.shs")).to_equal(true)
```

</details>

#### has a checked-in designated hot-path file set covering the real CPU hot paths

- has a checked-in designated hot-path file set covering the real CPU hot paths
   - Expected: file_exists("scripts/check/cpu_lane_hotpath_files.txt") is true
   - Expected: files contains `backend_software.spl`
   - Expected: files contains `backend_emu.spl`
   - Expected: files contains `compositor.spl`
   - Expected: files contains `helpers_text.spl`
   - Expected: files does not contain `famous_site_glyph_compositor.spl`
   - Expected: files contains `src/os/compositor/compositor.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has a checked-in designated hot-path file set covering the real CPU hot paths")
expect(file_exists("scripts/check/cpu_lane_hotpath_files.txt")).to_equal(true)
val files = read_file("scripts/check/cpu_lane_hotpath_files.txt")
expect(files.contains("backend_software.spl")).to_equal(true)
expect(files.contains("backend_emu.spl")).to_equal(true)
expect(files.contains("compositor.spl")).to_equal(true)
expect(files.contains("helpers_text.spl")).to_equal(true)
expect(files.contains("famous_site_glyph_compositor.spl")).to_equal(false)
expect(files.contains("src/os/compositor/compositor.spl")).to_equal(true)
```

</details>

<details>
<summary>Advanced: documents the four violation classes (LOOP / BYTE / SUBSTR / CHAIN)</summary>

#### documents the four violation classes (LOOP / BYTE / SUBSTR / CHAIN)

- documents the four violation classes (LOOP / BYTE / SUBSTR / CHAIN)
   - Expected: source contains `LOOP_PATTERN`
   - Expected: source contains `SUBSTR_PATTERN`
   - Expected: source contains `U8_DECL_PATTERN`
   - Expected: source contains `CHAIN_PATTERN`
   - Expected: source contains `cpu-lane-loop-ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("documents the four violation classes (LOOP / BYTE / SUBSTR / CHAIN)")
val source = read_file("scripts/check/check-cpu-hotloop-idiom.shs")
expect(source.contains("LOOP_PATTERN")).to_equal(true)
expect(source.contains("SUBSTR_PATTERN")).to_equal(true)
expect(source.contains("U8_DECL_PATTERN")).to_equal(true)
expect(source.contains("CHAIN_PATTERN")).to_equal(true)
expect(source.contains("cpu-lane-loop-ok")).to_equal(true)
```

</details>


</details>

#### documents the recursion blind spot instead of pretending coverage

- documents the recursion blind spot instead of pretending coverage
   - Expected: source contains `recursion`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("documents the recursion blind spot instead of pretending coverage")
val source = read_file("scripts/check/check-cpu-hotloop-idiom.shs")
expect(source.contains("recursion")).to_equal(true)
```

</details>

#### supports a baseline ratchet with update, file-list and baseline overrides

- supports a baseline ratchet with update, file-list and baseline overrides
   - Expected: source contains `cpu_lane_hotloop_baseline.txt`
   - Expected: source contains `--update-baseline`
   - Expected: source contains `--file-list`
   - Expected: source contains `--baseline`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("supports a baseline ratchet with update, file-list and baseline overrides")
val source = read_file("scripts/check/check-cpu-hotloop-idiom.shs")
expect(source.contains("cpu_lane_hotloop_baseline.txt")).to_equal(true)
expect(source.contains("--update-baseline")).to_equal(true)
expect(source.contains("--file-list")).to_equal(true)
expect(source.contains("--baseline")).to_equal(true)
```

</details>

#### reports machine-readable key=value status lines

- reports machine-readable key=value status lines
   - Expected: source contains `cpu_lane_hotloop_new=`
   - Expected: source contains `cpu_lane_hotloop_ok=`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports machine-readable key=value status lines")
val source = read_file("scripts/check/check-cpu-hotloop-idiom.shs")
expect(source.contains("cpu_lane_hotloop_new=")).to_equal(true)
expect(source.contains("cpu_lane_hotloop_ok=")).to_equal(true)
```

</details>

#### keeps a content-keyed baseline (COUNT<TAB>CLASS<TAB>file<TAB>text, no line numbers)

- keeps a content-keyed baseline (COUNT<TAB>CLASS<TAB>file<TAB>text, no line numbers)
   - Expected: file_exists("scripts/check/cpu_lane_hotloop_baseline.txt") is true
   - Expected: baseline contains `LOOP`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps a content-keyed baseline (COUNT<TAB>CLASS<TAB>file<TAB>text, no line numbers)")
expect(file_exists("scripts/check/cpu_lane_hotloop_baseline.txt")).to_equal(true)
val baseline = read_file("scripts/check/cpu_lane_hotloop_baseline.txt")
expect(baseline.contains("LOOP")).to_equal(true)
```

</details>

<details>
<summary>Advanced: flags a fresh unannotated per-element loop (LOOP)</summary>

#### flags a fresh unannotated per-element loop (LOOP)

- flags a fresh unannotated per-element loop (LOOP)
   - Expected: code equals `1`
   - Expected: out contains `cpu_lane_hotloop_new=1`
   - Expected: out contains `cpu_lane_hotloop_ok=false`
   - Expected: out contains `known_offender.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("flags a fresh unannotated per-element loop (LOOP)")
val (out, code) = _run_fixture("offender_file_list.txt")
expect(code).to_equal(1)
expect(out.contains("cpu_lane_hotloop_new=1")).to_equal(true)
expect(out.contains("cpu_lane_hotloop_ok=false")).to_equal(true)
expect(out.contains("known_offender.spl")).to_equal(true)
```

</details>


</details>

#### flags an idiomatic .for_each/.map/.each escape chain (CHAIN)

- flags an idiomatic .for_each/.map/.each escape chain (CHAIN)
   - Expected: code equals `1`
   - Expected: out contains `cpu_lane_hotloop_new=1`
   - Expected: out contains `chain_offender.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("flags an idiomatic .for_each/.map/.each escape chain (CHAIN)")
val (out, code) = _run_fixture("chain_file_list.txt")
expect(code).to_equal(1)
expect(out.contains("cpu_lane_hotloop_new=1")).to_equal(true)
expect(out.contains("chain_offender.spl")).to_equal(true)
```

</details>

<details>
<summary>Advanced: flags a multi-line parenthesized loop condition (LOOP, colon on a later line)</summary>

#### flags a multi-line parenthesized loop condition (LOOP, colon on a later line)

- flags a multi-line parenthesized loop condition (LOOP, colon on a later line)
   - Expected: code equals `1`
   - Expected: out contains `cpu_lane_hotloop_new=1`
   - Expected: out contains `multiline_offender.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("flags a multi-line parenthesized loop condition (LOOP, colon on a later line)")
val (out, code) = _run_fixture("multiline_file_list.txt")
expect(code).to_equal(1)
expect(out.contains("cpu_lane_hotloop_new=1")).to_equal(true)
expect(out.contains("multiline_offender.spl")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: keys each multi-line loop header distinctly instead of collapsing to `while (`</summary>

#### keys each multi-line loop header distinctly instead of collapsing to `while (`

- keys each multi-line loop header distinctly instead of collapsing to `while (`
   - Expected: code equals `1`
   - Expected: out contains `cpu_lane_hotloop_new=2`
   - Expected: out contains `while ( i < n and a < b ):`
   - Expected: out contains `while ( j < n and b > a ):`
   - Expected: out does not contain `multiline_distinct_offender.spl:while (\n`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keys each multi-line loop header distinctly instead of collapsing to `while (`")
val (out, code) = _run_fixture("multiline_distinct_file_list.txt")
expect(code).to_equal(1)
expect(out.contains("cpu_lane_hotloop_new=2")).to_equal(true)
expect(out.contains("while ( i < n and a < b ):")).to_equal(true)
expect(out.contains("while ( j < n and b > a ):")).to_equal(true)
expect(out.contains("multiline_distinct_offender.spl:while (\n")).to_equal(false)
```

</details>


</details>

#### flags byte indexing when the [u8] declaration is in the same file (BYTE)

- flags byte indexing when the [u8] declaration is in the same file (BYTE)
   - Expected: code equals `1`
   - Expected: out contains `cpu_lane_hotloop_new=1`
   - Expected: out contains `byte_offender.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("flags byte indexing when the [u8] declaration is in the same file (BYTE)")
val (out, code) = _run_fixture("byte_offender_file_list.txt")
expect(code).to_equal(1)
expect(out.contains("cpu_lane_hotloop_new=1")).to_equal(true)
expect(out.contains("byte_offender.spl")).to_equal(true)
```

</details>

#### does not leak a [u8] name into another designated file

- does not leak a [u8] name into another designated file
   - Expected: code equals `0`
   - Expected: out contains `cpu_lane_hotloop_new=0`
   - Expected: out contains `cpu_lane_hotloop_ok=true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("does not leak a [u8] name into another designated file")
val (out, code) = _run_fixture("byte_cross_file_list.txt")
expect(code).to_equal(0)
expect(out.contains("cpu_lane_hotloop_new=0")).to_equal(true)
expect(out.contains("cpu_lane_hotloop_ok=true")).to_equal(true)
```

</details>

<details>
<summary>Advanced: passes a clean fixture (loop annotated on its header + a loop-free fn)</summary>

#### passes a clean fixture (loop annotated on its header + a loop-free fn)

- passes a clean fixture (loop annotated on its header + a loop-free fn)
   - Expected: code equals `0`
   - Expected: out contains `cpu_lane_hotloop_new=0`
   - Expected: out contains `cpu_lane_hotloop_ok=true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("passes a clean fixture (loop annotated on its header + a loop-free fn)")
val (out, code) = _run_fixture("clean_file_list.txt")
expect(code).to_equal(0)
expect(out.contains("cpu_lane_hotloop_new=0")).to_equal(true)
expect(out.contains("cpu_lane_hotloop_ok=true")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: exempts a loop annotated on its HEADER line (new=0)</summary>

#### exempts a loop annotated on its HEADER line (new=0)

- exempts a loop annotated on its HEADER line (new=0)
   - Expected: code equals `0`
   - Expected: out contains `cpu_lane_hotloop_new=0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exempts a loop annotated on its HEADER line (new=0)")
val (out, code) = _run_fixture("header_ok_file_list.txt")
expect(code).to_equal(0)
expect(out.contains("cpu_lane_hotloop_new=0")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: does NOT exempt a loop when the annotation sits on the def line (new=1)</summary>

#### does NOT exempt a loop when the annotation sits on the def line (new=1)

- does NOT exempt a loop when the annotation sits on the def line (new=1)
   - Expected: code equals `1`
   - Expected: out contains `cpu_lane_hotloop_new=1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("does NOT exempt a loop when the annotation sits on the def line (new=1)")
val (out, code) = _run_fixture("def_annotated_file_list.txt")
expect(code).to_equal(1)
expect(out.contains("cpu_lane_hotloop_new=1")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: ratchets clean when a baselined loop has moved to a different line (new=0)</summary>

#### ratchets clean when a baselined loop has moved to a different line (new=0)

- ratchets clean when a baselined loop has moved to a different line (new=0)
   - Expected: code equals `0`
   - Expected: out contains `cpu_lane_hotloop_new=0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("ratchets clean when a baselined loop has moved to a different line (new=0)")
val (out, code) = _run_gate(["--file-list", "{FIX}/shift_file_list.txt", "--baseline", "{FIX}/shift_baseline.txt"])
expect(code).to_equal(0)
expect(out.contains("cpu_lane_hotloop_new=0")).to_equal(true)
```

</details>


</details>

#### ratchets clean on the real designated file set (baseline == current, new=0)

- ratchets clean on the real designated file set (baseline == current, new=0)
   - Expected: code equals `0`
   - Expected: out contains `cpu_lane_hotloop_new=0`
   - Expected: out contains `cpu_lane_hotloop_ok=true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("ratchets clean on the real designated file set (baseline == current, new=0)")
val (out, code) = _run_gate([])
expect(code).to_equal(0)
expect(out.contains("cpu_lane_hotloop_new=0")).to_equal(true)
expect(out.contains("cpu_lane_hotloop_ok=true")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/ui/feature/cpu_hotloop_gate_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering CPU-lane hot-loop enforcement gate (design §6.1 / plan W2).
- CPU-lane hot-loop enforcement gate (design §6.1 / plan W2)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2cf47d037d33636e15d5ae896ec7e16403bd9663c191f5d85b82b255b9f6d0ab`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2cf47d037d33636e15d5ae896ec7e16403bd9663c191f5d85b82b255b9f6d0ab`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2cf47d037d33636e15d5ae896ec7e16403bd9663c191f5d85b82b255b9f6d0ab`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **76/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/app/ui/feature/cpu_hotloop_gate_spec.spl
mirror: doc/06_spec/03_system/app/ui/feature/cpu_hotloop_gate_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=20
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=76; blocker cap makes effective=49
doc/06_spec/03_system/app/ui/feature/cpu_hotloop_gate_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/ui/feature/cpu_hotloop_gate_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/ui/feature/cpu_hotloop_gate_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/03_system/app/ui/feature/cpu_hotloop_gate_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 11 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/ui/feature/cpu_hotloop_gate_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has a gate script' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/ui/feature/cpu_hotloop_gate_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has a checked-in designated hot-path file set covering the real CPU hot paths' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/ui/feature/cpu_hotloop_gate_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'documents the four violation classes (LOOP / BYTE / SUBSTR / CHAIN)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
