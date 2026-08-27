# Wine Hello Dispatch Specification

> Tests covering Wine known hello fixture bridge.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Hello Dispatch Specification

## Scenarios

### Wine known hello fixture bridge

#### rejects PE bytes without the explicit hello marker

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects PE bytes without the explicit hello marker
   - Expected: wine_known_hello_fixture_gate(_zero_bytes(64)) equals `hello-fixture-marker-missing`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects PE bytes without the explicit hello marker")
expect(wine_known_hello_fixture_gate(_zero_bytes(64))).to_equal("hello-fixture-marker-missing")
```

</details>

#### accepts only the known hello milestone marker

- accepts only the known hello milestone marker
   - Expected: wine_known_hello_fixture_gate(data) equals `ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accepts only the known hello milestone marker")
val data = _put_stdout_payload(_put_marker(_zero_bytes(128), 8), 40, "Hello from SimpleOS Wine\n")
expect(wine_known_hello_fixture_gate(data)).to_equal("ready")
```

</details>

#### requires stdout payload bytes after the fixture marker

- requires stdout payload bytes after the fixture marker
   - Expected: wine_known_hello_fixture_gate(_put_marker(_zero_bytes(64), 8)) equals `hello-stdout-payload-missing`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("requires stdout payload bytes after the fixture marker")
expect(wine_known_hello_fixture_gate(_put_marker(_zero_bytes(64), 8))).to_equal("hello-stdout-payload-missing")
```

</details>

#### extracts the milestone stdout from fixture bytes

- extracts the milestone stdout from fixture bytes
   - Expected: wine_known_hello_stdout_payload(data) equals `Hello from SimpleOS Wine\n`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("extracts the milestone stdout from fixture bytes")
val data = _put_stdout_payload(_put_marker(_zero_bytes(128), 8), 40, "Hello from SimpleOS Wine\n")
expect(wine_known_hello_stdout_payload(data)).to_equal("Hello from SimpleOS Wine\n")
```

</details>

#### extracts stdout only from the decoded payload RVA

- extracts stdout only from the decoded payload RVA
   - Expected: wine_known_hello_stdout_payload_at_rva(data, 0x2120) equals `Hello from SimpleOS Wine\n`
   - Expected: wine_known_hello_stdout_payload_at_rva(data, 0x2130) equals ``
   - Expected: wine_known_hello_fixture_gate_at_rva(data, 0x2130) equals `hello-stdout-payload-rva-mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("extracts stdout only from the decoded payload RVA")
val data = _put_stdout_payload(_put_marker(_put_pe_mapping(_zero_bytes(1024)), 0x300), 0x320, "Hello from SimpleOS Wine\n")
expect(wine_known_hello_stdout_payload_at_rva(data, 0x2120)).to_equal("Hello from SimpleOS Wine\n")
expect(wine_known_hello_stdout_payload_at_rva(data, 0x2130)).to_equal("")
expect(wine_known_hello_fixture_gate_at_rva(data, 0x2130)).to_equal("hello-stdout-payload-rva-mismatch")
```

</details>

#### returns the milestone stdout for the known fixture

- returns the milestone stdout for the known fixture
   - Expected: wine_known_hello_stdout(data) equals `Hello from SimpleOS Wine\n`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns the milestone stdout for the known fixture")
val data = _put_stdout_payload(_put_marker(_zero_bytes(128), 8), 40, "Hello from SimpleOS Wine\n")
expect(wine_known_hello_stdout(data)).to_equal("Hello from SimpleOS Wine\n")
```

</details>

#### returns stdout only through the decoded payload RVA

- returns stdout only through the decoded payload RVA
   - Expected: wine_known_hello_stdout_at_rva(data, 0x2120) equals `Hello from SimpleOS Wine\n`
   - Expected: wine_known_hello_stdout_at_rva(data, 0x2130) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns stdout only through the decoded payload RVA")
val data = _put_stdout_payload(_put_marker(_put_pe_mapping(_zero_bytes(1024)), 0x300), 0x320, "Hello from SimpleOS Wine\n")
expect(wine_known_hello_stdout_at_rva(data, 0x2120)).to_equal("Hello from SimpleOS Wine\n")
expect(wine_known_hello_stdout_at_rva(data, 0x2130)).to_equal("")
```

</details>

#### gates execution on the decoded stdout payload without requiring the fixture marker

- gates execution on the decoded stdout payload without requiring the fixture marker
   - Expected: wine_hello_stdout_payload_gate_at_rva(data, 0x2120) equals `ready`
   - Expected: wine_hello_stdout_payload_gate_at_rva(data, 0x2130) equals `hello-stdout-payload-rva-mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("gates execution on the decoded stdout payload without requiring the fixture marker")
val data = _put_stdout_payload(_put_pe_mapping(_zero_bytes(1024)), 0x320, "Hello from SimpleOS Wine\n")
expect(wine_hello_stdout_payload_gate_at_rva(data, 0x2120)).to_equal("ready")
expect(wine_hello_stdout_payload_gate_at_rva(data, 0x2130)).to_equal("hello-stdout-payload-rva-mismatch")
```

</details>

#### returns structured execution evidence through the decoded payload RVA

- returns structured execution evidence through the decoded payload RVA
   - Expected: result.ok is true
   - Expected: result.bytes_written equals `25`
   - Expected: result.exit_code equals `0`
   - Expected: result.stdout equals `Hello from SimpleOS Wine\n`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns structured execution evidence through the decoded payload RVA")
val data = _put_stdout_payload(_put_marker(_put_pe_mapping(_zero_bytes(1024)), 0x300), 0x320, "Hello from SimpleOS Wine\n")
val result = wine_known_hello_execute_at_rva(data, 0x2120)
expect(result.ok).to_equal(true)
expect(result.bytes_written).to_equal(25)
expect(result.exit_code).to_equal(0)
expect(result.stdout).to_equal("Hello from SimpleOS Wine\n")
```

</details>

#### executes only through a valid CPU hello execution plan

- executes only through a valid CPU hello execution plan
   - Expected: result.ok is true
   - Expected: result.stdout equals `Hello from SimpleOS Wine\n`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("executes only through a valid CPU hello execution plan")
var data = _put_stdout_payload(_put_marker(_put_pe_mapping(_zero_bytes(1024)), 0x300), 0x320, "Hello from SimpleOS Wine\n")
data[0x200] = 0x48
data[0x201] = 0x31
data[0x202] = 0xc9
data[0x203] = 0xff
data[0x204] = 0x15
data = _put_u32_le(data, 0x205, 0x2060 - 0x2009)
data[0x209] = 0x48
data[0x20a] = 0x8d
data[0x20b] = 0x15
data = _put_u32_le(data, 0x20c, 0x2120 - 0x2010)
data[0x210] = 0xff
data[0x211] = 0x15
data = _put_u32_le(data, 0x212, 0x2068 - 0x2016)
data[0x216] = 0x31
data[0x217] = 0xc9
data[0x218] = 0xff
data[0x219] = 0x15
data = _put_u32_le(data, 0x21a, 0x2070 - 0x201e)
val plan = wine_cpu_hello_execution_plan(data, "thread-context thread-context-rip thread-context-rsp thread-context-registers-zeroed thread-context-teb-bound user-stack user-stack-allocated user-stack-committed user-stack-guard-page user-stack-aligned entrypoint-mapped entrypoint-rva-valid entrypoint-section-executable entrypoint-window-readable import-thunks-bound import-module-loaded import-module-handle-valid import-module-loader-sequence import-thunk-table-valid import-thunk-symbols-resolved import-thunk-bindings-match import-thunk-iat-guarded stdout-handle stdout-handle-std-output stdout-handle-writable stdout-byte-count-checked stdout-write-guarded exit-trap exit-trap-process-exit exit-trap-status-code exit-trap-no-fallthrough no-native-jump no-native-jump-import-targets no-native-jump-entry-bounds no-native-jump-host-code-blocked win64-abi win64-abi-register-args win64-abi-shadow-space win64-abi-stack-align win64-abi-return-value win64-abi-guarded-call x86_64-decoder x86_64-decode-window-mapped x86_64-decode-window-bounded x86_64-decode-supported-ops x86_64-decode-call-targets x86_64-dispatch x86_64-dispatch-no-native-jump x86_64-dispatch-import-calls-only x86_64-dispatch-exit-trap x86_64-dispatch-stdout-sequence")
val result = wine_known_hello_execute_plan(data, plan)
expect(result.ok).to_equal(true)
expect(result.stdout).to_equal("Hello from SimpleOS Wine\n")
```

</details>

#### rejects CPU hello plans with reordered or mismatched decoded call metadata

- rejects CPU hello plans with reordered or mismatched decoded call metadata
   - Expected: wine_known_hello_execute_plan(data, reordered).error equals `bridge-sequence-expected:GetStdHandle`
   - Expected: wine_known_hello_execute_plan(data, count_mismatch).error equals `bridge-sequence-count-mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects CPU hello plans with reordered or mismatched decoded call metadata")
val data = _put_stdout_payload(_put_marker(_put_pe_mapping(_zero_bytes(1024)), 0x300), 0x320, "Hello from SimpleOS Wine\n")
val reordered = WineCpuHelloExecutionPlan(ok: true, error: "", entry_rva: 0x2000, sequence_rva: 0x2000, sequence_end_rva: 0x201e, instruction_sequence: "xor-rcx-rcx call-rip-indirect lea-rdx-rip-rel32 call-rip-indirect xor-ecx-ecx call-rip-indirect", instruction_count: 6, call_sequence: "WriteFile GetStdHandle ExitProcess", call_count: 3, get_std_handle_rva: 0x2060, stdout_payload_rva: 0x2120, write_file_rva: 0x2068, exit_process_rva: 0x2070)
val count_mismatch = WineCpuHelloExecutionPlan(ok: true, error: "", entry_rva: 0x2000, sequence_rva: 0x2000, sequence_end_rva: 0x201e, instruction_sequence: "xor-rcx-rcx call-rip-indirect", instruction_count: 2, call_sequence: "GetStdHandle WriteFile ExitProcess", call_count: 2, get_std_handle_rva: 0x2060, stdout_payload_rva: 0x2120, write_file_rva: 0x2068, exit_process_rva: 0x2070)
expect(wine_known_hello_execute_plan(data, reordered).error).to_equal("bridge-sequence-expected:GetStdHandle")
expect(wine_known_hello_execute_plan(data, count_mismatch).error).to_equal("bridge-sequence-count-mismatch")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_hello_dispatch_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Wine known hello fixture bridge.
- Wine known hello fixture bridge

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
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

- Canonical SPipe generation for source `f8e58c1bbd86fef03ceb29c04f252a40d135771cbeab0aec836ca39a9945bafe`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f8e58c1bbd86fef03ceb29c04f252a40d135771cbeab0aec836ca39a9945bafe`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f8e58c1bbd86fef03ceb29c04f252a40d135771cbeab0aec836ca39a9945bafe`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/common/wine_hello_dispatch_spec.spl
mirror: doc/06_spec/01_unit/lib/common/wine_hello_dispatch_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/wine_hello_dispatch_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/wine_hello_dispatch_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/wine_hello_dispatch_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/wine_hello_dispatch_spec.spl:103:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects PE bytes without the explicit hello marker' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/wine_hello_dispatch_spec.spl:108:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts only the known hello milestone marker' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/wine_hello_dispatch_spec.spl:114:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires stdout payload bytes after the fixture marker' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
