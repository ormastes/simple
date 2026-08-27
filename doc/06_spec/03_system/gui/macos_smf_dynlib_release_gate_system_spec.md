# macOS GUI SMF Dynlib Release Gate System Spec

> Runs the macOS SMF dynlib release gate. On macOS arm64 this must produce the

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# macOS GUI SMF Dynlib Release Gate System Spec

Runs the macOS SMF dynlib release gate. On macOS arm64 this must produce the

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/macos_smf_dynlib_release_gate_system_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Runs the macOS SMF dynlib release gate. On macOS arm64 this must produce the
full passing release transcript. On other hosts it must fail explicitly with the
platform skip evidence row, so non-mac CI cannot accidentally claim mac release
evidence.

## Scenarios

### macOS GUI SMF dynlib release gate

<details>
<summary>Advanced: passes only with mac release evidence and otherwise reports an explicit platform skip</summary>

#### passes only with mac release evidence and otherwise reports an explicit platform skip _(slow)_

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- passes only with mac release evidence and otherwise reports an explicit platform skip
   - Expected: code equals `0`
   - Expected: stdout contains `GUI_MAC_SMF_DYNLIB_RELEASE_GATE status=pass`
   - Expected: stdout contains `GUI_MAC_SMF_DYNLIB_TRANSCRIPT status=pass`
   - Expected: stdout contains `loader=smf_dynlib`
   - Expected: stdout contains `dynload=smf_dynlib`
   - Expected: stdout contains `host_dynload=sffi`
   - Expected: stdout contains `call_source=dynlib_symbol_call`
   - Expected: stdout contains `"transcript=" + _transcript_path()`
   - Expected: gui_mac_smf_dynlib_accepts_transcript(transcript) is true
   - Expected: transcript_check[2] equals `0`
   - Expected: transcript_check[0] contains `GUI_MAC_SMF_DYNLIB_TRANSCRIPT status=pass`
   - Expected: gui_mac_smf_dynlib_row_has(probe, "artifact", "build/gui/pure_gui_hot.smf") is true
   - Expected: gui_mac_smf_dynlib_row_has(probe, "dynlib_path", "build/gui/pure_gui_hot.smf.extracted.dylib") is true
   - Expected: gui_mac_smf_dynlib_row_has(probe, "loader", "smf_dynlib") is true
   - Expected: gui_mac_smf_dynlib_row_has(probe, "dynload", "smf_dynlib") is true
   - Expected: gui_mac_smf_dynlib_row_has(probe, "host_dynload", "sffi") is true
   - Expected: gui_mac_smf_dynlib_row_has(probe, "call_source", "dynlib_symbol_call") is true
   - Expected: gui_mac_smf_dynlib_row_has(probe, "samples", "128") is true
   - Expected: gui_mac_smf_dynlib_row_has(probe, "expected_samples", "128") is true
   - Expected: gui_mac_smf_dynlib_row_has(probe, "threshold_us", "1000") is true
   - Expected: code equals `1`
   - Expected: stdout contains `GUI_MAC_SMF_DYNLIB_EVIDENCE status=skip`
   - Expected: stdout contains `reason=requires-macos-arm64`
   - Expected: stdout contains `GUI_MAC_SMF_DYNLIB_RELEASE_GATE status=fail reason=transcript-check-failed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("passes only with mac release evidence and otherwise reports an explicit platform skip")
val result = _run_gate()
val stdout = result[0]
val stderr = result[1]
val code = result[2]
val host_os = host_os()
if host_os == "macos":
    if code != 0:
        print "macos_smf_dynlib_release_gate stdout: " + stdout
        print "macos_smf_dynlib_release_gate stderr: " + stderr
    expect(code).to_equal(0)
    expect(stdout.contains("GUI_MAC_SMF_DYNLIB_RELEASE_GATE status=pass")).to_equal(true)
    expect(stdout.contains("GUI_MAC_SMF_DYNLIB_TRANSCRIPT status=pass")).to_equal(true)
    expect(stdout.contains("loader=smf_dynlib")).to_equal(true)
    expect(stdout.contains("dynload=smf_dynlib")).to_equal(true)
    expect(stdout.contains("host_dynload=sffi")).to_equal(true)
    expect(stdout.contains("call_source=dynlib_symbol_call")).to_equal(true)
    expect(stdout.contains("transcript=" + _transcript_path())).to_equal(true)
    val transcript = file_read_text(_transcript_path())
    expect(gui_mac_smf_dynlib_accepts_transcript(transcript)).to_equal(true)
    val transcript_check = _run_transcript_check()
    expect(transcript_check[2]).to_equal(0)
    expect(transcript_check[0].contains("GUI_MAC_SMF_DYNLIB_TRANSCRIPT status=pass")).to_equal(true)
    val probe = gui_mac_smf_dynlib_select_stdout_row(transcript, "GUI_DYNLIB_PERF")
    expect(gui_mac_smf_dynlib_row_has(probe, "artifact", "build/gui/pure_gui_hot.smf")).to_equal(true)
    expect(gui_mac_smf_dynlib_row_has(probe, "dynlib_path", "build/gui/pure_gui_hot.smf.extracted.dylib")).to_equal(true)
    expect(gui_mac_smf_dynlib_row_has(probe, "loader", "smf_dynlib")).to_equal(true)
    expect(gui_mac_smf_dynlib_row_has(probe, "dynload", "smf_dynlib")).to_equal(true)
    expect(gui_mac_smf_dynlib_row_has(probe, "host_dynload", "sffi")).to_equal(true)
    expect(gui_mac_smf_dynlib_row_has(probe, "call_source", "dynlib_symbol_call")).to_equal(true)
    expect(gui_mac_smf_dynlib_row_has(probe, "samples", "128")).to_equal(true)
    expect(gui_mac_smf_dynlib_row_has(probe, "expected_samples", "128")).to_equal(true)
    expect(gui_mac_smf_dynlib_row_has(probe, "threshold_us", "1000")).to_equal(true)
    expect(gui_mac_smf_dynlib_row_unsigned_i64(probe, "p99_us")).to_be_less_than(1000)
else:
    expect(code).to_equal(1)
    expect(stdout.contains("GUI_MAC_SMF_DYNLIB_EVIDENCE status=skip")).to_equal(true)
    expect(stdout.contains("reason=requires-macos-arm64")).to_equal(true)
    expect(stdout.contains("GUI_MAC_SMF_DYNLIB_RELEASE_GATE status=fail reason=transcript-check-failed")).to_equal(true)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 1 |
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

- Canonical SPipe generation for source `16c4d8161229d77c7e0b13cbd1b2aa17328532340e8f0645a87b7b5394fda463`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `16c4d8161229d77c7e0b13cbd1b2aa17328532340e8f0645a87b7b5394fda463`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `16c4d8161229d77c7e0b13cbd1b2aa17328532340e8f0645a87b7b5394fda463`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/03_system/gui/macos_smf_dynlib_release_gate_system_spec.spl
mirror: doc/06_spec/03_system/gui/macos_smf_dynlib_release_gate_system_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/gui/macos_smf_dynlib_release_gate_system_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gui/macos_smf_dynlib_release_gate_system_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gui/macos_smf_dynlib_release_gate_system_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/gui/macos_smf_dynlib_release_gate_system_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'passes only with mac release evidence and otherwise reports an explicit platform skip' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
