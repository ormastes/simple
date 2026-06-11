# Wine Hello Dispatch Specification

> <details>

<!-- sdn-diagram:id=wine_hello_dispatch_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_hello_dispatch_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_hello_dispatch_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_hello_dispatch_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Hello Dispatch Specification

## Scenarios

### Wine known hello fixture bridge

#### rejects PE bytes without the explicit hello marker

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(wine_known_hello_fixture_gate(_zero_bytes(64))).to_equal("hello-fixture-marker-missing")
```

</details>

#### accepts only the known hello milestone marker

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = _put_stdout_payload(_put_marker(_zero_bytes(128), 8), 40, "Hello from SimpleOS Wine\n")
expect(wine_known_hello_fixture_gate(data)).to_equal("ready")
```

</details>

#### requires stdout payload bytes after the fixture marker

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(wine_known_hello_fixture_gate(_put_marker(_zero_bytes(64), 8))).to_equal("hello-stdout-payload-missing")
```

</details>

#### extracts the milestone stdout from fixture bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = _put_stdout_payload(_put_marker(_zero_bytes(128), 8), 40, "Hello from SimpleOS Wine\n")
expect(wine_known_hello_stdout_payload(data)).to_equal("Hello from SimpleOS Wine\n")
```

</details>

#### extracts stdout only from the decoded payload RVA

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = _put_stdout_payload(_put_marker(_put_pe_mapping(_zero_bytes(1024)), 0x300), 0x320, "Hello from SimpleOS Wine\n")
expect(wine_known_hello_stdout_payload_at_rva(data, 0x2120)).to_equal("Hello from SimpleOS Wine\n")
expect(wine_known_hello_stdout_payload_at_rva(data, 0x2130)).to_equal("")
expect(wine_known_hello_fixture_gate_at_rva(data, 0x2130)).to_equal("hello-stdout-payload-rva-mismatch")
```

</details>

#### returns the milestone stdout for the known fixture

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = _put_stdout_payload(_put_marker(_zero_bytes(128), 8), 40, "Hello from SimpleOS Wine\n")
expect(wine_known_hello_stdout(data)).to_equal("Hello from SimpleOS Wine\n")
```

</details>

#### returns stdout only through the decoded payload RVA

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = _put_stdout_payload(_put_marker(_put_pe_mapping(_zero_bytes(1024)), 0x300), 0x320, "Hello from SimpleOS Wine\n")
expect(wine_known_hello_stdout_at_rva(data, 0x2120)).to_equal("Hello from SimpleOS Wine\n")
expect(wine_known_hello_stdout_at_rva(data, 0x2130)).to_equal("")
```

</details>

#### gates execution on the decoded stdout payload without requiring the fixture marker

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = _put_stdout_payload(_put_pe_mapping(_zero_bytes(1024)), 0x320, "Hello from SimpleOS Wine\n")
expect(wine_hello_stdout_payload_gate_at_rva(data, 0x2120)).to_equal("ready")
expect(wine_hello_stdout_payload_gate_at_rva(data, 0x2130)).to_equal("hello-stdout-payload-rva-mismatch")
```

</details>

#### returns structured execution evidence through the decoded payload RVA

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = _put_stdout_payload(_put_marker(_put_pe_mapping(_zero_bytes(1024)), 0x300), 0x320, "Hello from SimpleOS Wine\n")
val result = wine_known_hello_execute_at_rva(data, 0x2120)
expect(result.ok).to_equal(true)
expect(result.bytes_written).to_equal(25)
expect(result.exit_code).to_equal(0)
expect(result.stdout).to_equal("Hello from SimpleOS Wine\n")
```

</details>

#### executes only through a valid CPU hello execution plan

1. var data =  put stdout payload
2. data =  put u32 le
3. data =  put u32 le
4. data =  put u32 le
5. data =  put u32 le
   - Expected: result.ok is true
   - Expected: result.stdout equals `Hello from SimpleOS Wine\n`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
