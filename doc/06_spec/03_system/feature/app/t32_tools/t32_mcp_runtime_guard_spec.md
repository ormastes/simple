# T32 MCP Runtime Guard Tests

> Guards against T32 MCP server runtime failures: `rt_time_now_unix_micros() / 1000` wrapper must use `stdout_write()` instead

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# T32 MCP Runtime Guard Tests

Guards against T32 MCP server runtime failures: `rt_time_now_unix_micros() / 1000` wrapper must use `stdout_write()` instead

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #T32-MCP-RUNTIME-001 |
| Category | Tooling |
| Difficulty | 2/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | N/A |
| Source | `test/03_system/feature/app/t32_tools/t32_mcp_runtime_guard_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Guards against T32 MCP server runtime failures:
- Bug 11: `rt_time_ms()` missing in native runtime — replaced with
  `rt_time_now_unix_micros() / 1000` wrapper
- Bug 12: Process hangs silently — debug mode default flipped to ON
- Bug 13: `rt_file_append_text("/proc/self/fd/1")` fails for stdout —
  must use `stdout_write()` instead
- Guard: All extern fns used by T32 MCP modules must exist in native runtime

## Source

- `examples/10_tooling/trace32_tools/t32_mcp/job_manager.spl`
- `examples/10_tooling/trace32_tools/t32_mcp/snapshot_store.spl`
- `examples/10_tooling/trace32_tools/t32_mcp/frontend_cold.spl`
- `examples/10_tooling/trace32_tools/t32_mcp/protocol.spl`

## Scenarios

### Bug 11 — rt_time_ms native availability

#### rt_time_now_unix_micros (actual runtime function)

#### returns a positive value

- returns a positive value
   - Expected: micros > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns a positive value")
val micros = rt_time_now_unix_micros()
expect(micros > 0).to_equal(true)
```

</details>

#### returns a plausible epoch timestamp

- returns a plausible epoch timestamp
   - Expected: micros > 1704067200000000 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns a plausible epoch timestamp")
# After 2024-01-01 in microseconds = 1_704_067_200_000_000
val micros = rt_time_now_unix_micros()
expect(micros > 1704067200000000).to_equal(true)
```

</details>

#### rt_time_ms (wrapper in job_manager)

#### returns a positive value

- returns a positive value
   - Expected: ms > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns a positive value")
val ms = rt_time_ms()
expect(ms > 0).to_equal(true)
```

</details>

#### is roughly micros / 1000

- is roughly micros / 1000
   - Expected: diff > -1000 is true
   - Expected: diff < 1000 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("is roughly micros / 1000")
val micros = rt_time_now_unix_micros()
val ms = rt_time_ms()
# Should be within 1 second of each other
val diff = ms - (micros / 1000)
expect(diff > -1000).to_equal(true)
expect(diff < 1000).to_equal(true)
```

</details>

### Bug 12 — debug mode defaults to ON

#### t32_debug_enabled (frontend_cold)

#### returns true when T32_MCP_DEBUG_LOG is unset

- returns true when T32_MCP_DEBUG_LOG is unset
   - Expected: enabled is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns true when T32_MCP_DEBUG_LOG is unset")
# When the env var is not set, debug should default to ON
# so that silent hangs produce stderr output
val enabled = t32_debug_enabled()
expect(enabled).to_equal(true)
```

</details>

### Bug 13 — stdout_write extern exists

#### stdout_write extern fn

#### is callable and returns non-negative

- is callable and returns non-negative
   - Expected: result >= 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("is callable and returns non-negative")
# Writing an empty string should succeed (return >= 0)
val result = stdout_write("")
expect(result >= 0).to_equal(true)
```

</details>

#### rt_stdout_flush extern fn

#### is callable

- is callable
   - Expected: result >= 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("is callable")
val result = rt_stdout_flush()
# flush returns 0 on success
expect(result >= 0).to_equal(true)
```

</details>

### T32 MCP extern fn guard — prevents missing-function bugs

#### I/O functions

#### stderr_write exists

- stderr_write exists
   - Expected: r >= 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("stderr_write exists")
val r = stderr_write("")
expect(r >= 0).to_equal(true)
```

</details>

#### stderr_flush exists

- stderr_flush exists
   - Expected: r >= 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("stderr_flush exists")
val r = stderr_flush()
expect(r >= 0).to_equal(true)
```

</details>

#### environment functions

#### rt_env_get exists

- rt_env_get exists
   - Expected: home.len() >= 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rt_env_get exists")
val home = rt_env_get("HOME") ?? ""
# Should return something (or empty), not crash
expect(home.len() >= 0).to_equal(true)
```

</details>

#### rt_env_cwd exists

- rt_env_cwd exists
   - Expected: cwd.len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rt_env_cwd exists")
val cwd = rt_env_cwd()
expect(cwd.len() > 0).to_equal(true)
```

</details>

#### file I/O functions

#### rt_file_exists exists

- rt_file_exists exists
   - Expected: found is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rt_file_exists exists")
# /tmp always exists on Linux
val found = rt_file_exists("/tmp")
expect(found).to_equal(true)
```

</details>

#### rt_file_write_text exists

- rt_file_write_text exists
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rt_file_write_text exists")
val path = "/tmp/t32_mcp_test_guard_write.txt"
val ok = rt_file_write_text(path, "guard_test")
expect(ok).to_equal(true)
```

</details>

#### rt_file_append_text exists

- rt_file_append_text exists
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rt_file_append_text exists")
val path = "/tmp/t32_mcp_test_guard_write.txt"
val ok = rt_file_append_text(path, "\nappend_test")
expect(ok).to_equal(true)
```

</details>

#### process functions

#### rt_process_run exists

- rt_process_run exists
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rt_process_run exists")
val (stdout, stderr, code) = rt_process_run("/bin/echo", ["guard_test"])
expect(code).to_equal(0)
expect(stdout).to_contain("guard_test")
```

</details>

#### time functions

#### rt_time_now_unix_micros exists and returns epoch

- rt_time_now_unix_micros exists and returns epoch
   - Expected: micros > 1704067200000000 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rt_time_now_unix_micros exists and returns epoch")
val micros = rt_time_now_unix_micros()
expect(micros > 1704067200000000).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
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

- Canonical SPipe generation for source `9f50ab24ce484bbff9542f9cfdb333613926891b7b2794c5b6f09c04507ca22c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9f50ab24ce484bbff9542f9cfdb333613926891b7b2794c5b6f09c04507ca22c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9f50ab24ce484bbff9542f9cfdb333613926891b7b2794c5b6f09c04507ca22c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/feature/app/t32_tools/t32_mcp_runtime_guard_spec.spl
mirror: doc/06_spec/03_system/feature/app/t32_tools/t32_mcp_runtime_guard_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/app/t32_tools/t32_mcp_runtime_guard_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/app/t32_tools/t32_mcp_runtime_guard_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/app/t32_tools/t32_mcp_runtime_guard_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/app/t32_tools/t32_mcp_runtime_guard_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns a positive value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/app/t32_tools/t32_mcp_runtime_guard_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns a plausible epoch timestamp' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/app/t32_tools/t32_mcp_runtime_guard_spec.spl:83:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns a positive value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
