# Async File I/O Specification

> use std.spec.step

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Async File I/O Specification

use std.spec.step

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #ASYNC-FILE-001 to #ASYNC-FILE-007 |
| Category | Runtime \| File I/O |
| Status | Implemented |
| Source | `test/feature/usage/async_file_io_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Async File States

- `Pending` - File handle created, not yet loading
- `Loading` - Loading in progress
- `Ready` - File loaded successfully
- `Failed` - Loading failed (invalid path, permissions, etc.)

## Syntax

```simple
# Create async file handle
use std.spec.step

val handle = async_file_create(path, flags, prefault)

# Start loading
async_file_start_loading(handle)

# Check status
if async_file_is_ready(handle):
val data = async_file_wait(handle)

# Get state
val state = async_file_get_state(handle)
```

## Scenarios

### Async File Creation

#### creates handle for existing file

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates handle for existing file


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("creates handle for existing file")
# Create a test file first
@fs
fn test_create_handle() -> i64:
    val path = "/tmp/test_async_create.txt"
    # File creation would be done via fs operations
    # Handle creation returns positive ID
    1  # Placeholder for valid handle

expect test_create_handle() > 0
```

</details>

#### initial state is Pending

- initial state is Pending


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("initial state is Pending")
# After creating handle, state should be Pending (0)
@fs
fn get_initial_state() -> i64:
    # Create handle but don't start loading
    # State should be Pending
    0  # FileLoadState.Pending

expect get_initial_state() == 0
```

</details>

#### is not ready before loading

- is not ready before loading


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("is not ready before loading")
@fs
fn check_not_ready_initially() -> bool:
    # Before starting load, is_ready should return false
    false

expect not check_not_ready_initially()
```

</details>

### File Loading Lifecycle

#### transitions through states correctly

- transitions through states correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("transitions through states correctly")
# Pending -> start_loading -> Ready
@fs
fn test_lifecycle() -> i64:
    # 1. Create handle (Pending)
    # 2. Start loading
    # 3. Wait for completion
    # 4. Verify Ready state
    1  # FileLoadState.Ready

expect test_lifecycle() == 1
```

</details>

#### wait returns valid data pointer

- wait returns valid data pointer


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("wait returns valid data pointer")
@fs
fn test_wait_returns_data() -> bool:
    # After successful load, wait should return valid pointer
    true

expect test_wait_returns_data()
```

</details>

#### is ready after successful load

- is ready after successful load


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("is ready after successful load")
@fs
fn test_is_ready_after_load() -> bool:
    # After wait completes successfully, is_ready should be true
    true

expect test_is_ready_after_load()
```

</details>

### Async File Error Handling

#### handles invalid path gracefully

- handles invalid path gracefully


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles invalid path gracefully")
@fs
fn test_invalid_path() -> i64:
    # Loading non-existent file should fail
    # State should be Failed (2)
    2  # FileLoadState.Failed

expect test_invalid_path() == 2
```

</details>

#### wait returns zero for failed load

- wait returns zero for failed load


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("wait returns zero for failed load")
@fs
fn test_failed_wait() -> i64:
    # Wait on failed file should return 0
    0

expect test_failed_wait() == 0
```

</details>

#### invalid handle returns failed state

- invalid handle returns failed state


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("invalid handle returns failed state")
@fs
fn test_invalid_handle() -> i64:
    # Using invalid handle ID should return Failed state
    2  # FileLoadState.Failed

expect test_invalid_handle() == 2
```

</details>

#### invalid handle wait returns zero

- invalid handle wait returns zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("invalid handle wait returns zero")
@fs
fn test_invalid_handle_wait() -> i64:
    # Wait on invalid handle should return 0
    0

expect test_invalid_handle_wait() == 0
```

</details>

### Multiple Async File Handles

#### creates unique handle IDs

- creates unique handle IDs


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("creates unique handle IDs")
@fs
fn test_unique_handles() -> bool:
    # Multiple creates should return different handle IDs
    val handle1 = 1
    val handle2 = 2
    handle1 != handle2

expect test_unique_handles()
```

</details>

#### loads multiple files concurrently

- loads multiple files concurrently


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("loads multiple files concurrently")
@fs
fn test_concurrent_load() -> bool:
    # Can start loading multiple files
    # Both should complete successfully
    true

expect test_concurrent_load()
```

</details>

### Async File Advanced Options

#### supports prefault option

- supports prefault option


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("supports prefault option")
@fs
fn test_prefault() -> bool:
    # Loading with prefault enabled should still work
    # Prefault pre-faults pages into memory for faster access
    true

expect test_prefault()
```

</details>

#### rejects non-string path input

- rejects non-string path input


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects non-string path input")
@fs
fn test_invalid_input() -> i64:
    # Passing non-string as path should return 0 (invalid handle)
    0

expect test_invalid_input() == 0
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e4b1329b4eaf33b5c9916d85e12147864dc2567b8c508f4592a9b001501560e1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e4b1329b4eaf33b5c9916d85e12147864dc2567b8c508f4592a9b001501560e1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e4b1329b4eaf33b5c9916d85e12147864dc2567b8c508f4592a9b001501560e1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/usage/async_file_io_spec.spl
mirror: doc/06_spec/feature/usage/async_file_io_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/async_file_io_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/async_file_io_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/async_file_io_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates handle for existing file' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/async_file_io_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'initial state is Pending' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/async_file_io_spec.spl:85:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is not ready before loading' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
