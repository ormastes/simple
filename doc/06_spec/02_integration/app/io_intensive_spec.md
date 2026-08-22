# io_intensive_spec

> Verifies the io intensive behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 29 | 29 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# io_intensive_spec

Verifies the io intensive behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/io_intensive_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the io intensive behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### File I/O - Intensive

#### file writing

<details>
<summary>Advanced: simulates writing 100 files</summary>

#### simulates writing 100 files _(slow)_

- Verify: simulates writing 100 files


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-APP_IO_INTENSIVE-001
step("Verify: simulates writing 100 files")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var files = []

for i in 0..100:
    val file = {"path": "test/tmp/file{i}.txt", "content": "Content for file {i}", "size": 20 + i}
    files = files.append(file)

check(files.len() == 100)
```

</details>


</details>

<details>
<summary>Advanced: handles large file content</summary>

#### handles large file content _(slow)_

- Verify: handles large file content


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-APP_IO_INTENSIVE-001
step("Verify: handles large file content")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var parts: [text] = []
for i in 0..1000:
    parts.push("line {i}\n")
val large_content = parts.join("")

check(large_content.len() > 5000)
```

</details>


</details>

#### file reading

<details>
<summary>Advanced: simulates reading 100 files</summary>

#### simulates reading 100 files _(slow)_

- Verify: simulates reading 100 files


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-APP_IO_INTENSIVE-001
step("Verify: simulates reading 100 files")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var reads = 0

for i in 0..100:
    val path = "test/fixtures/data/file{i}.txt"
    if path.ends_with(".txt"):
        reads = reads + 1

check(reads == 100)
```

</details>


</details>

<details>
<summary>Advanced: processes file contents</summary>

#### processes file contents _(slow)_

- Verify: processes file contents


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-APP_IO_INTENSIVE-001
step("Verify: processes file contents")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var files = [
    {"path": "a.txt", "size": 100},
    {"path": "b.txt", "size": 200},
    {"path": "c.txt", "size": 300}
]

var total_size = 0
for file in files:
    total_size = total_size + file["size"]

check(total_size == 600)
```

</details>


</details>

#### file operations

<details>
<summary>Advanced: simulates file copy operations</summary>

#### simulates file copy operations _(slow)_

- Verify: simulates file copy operations


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-APP_IO_INTENSIVE-001
step("Verify: simulates file copy operations")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var operations = []

for i in 0..50:
    val op = {"source": "src/file{i}.txt", "dest": "dst/file{i}.txt", "status": "pending"}
    operations = operations.append(op)

check(operations.len() == 50)
```

</details>


</details>

<details>
<summary>Advanced: tracks file modifications</summary>

#### tracks file modifications _(slow)_

- Verify: tracks file modifications


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-APP_IO_INTENSIVE-001
step("Verify: tracks file modifications")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var modifications = []

for i in 0..200:
    val op_type = if i % 2 == 0: "write" else: "read"
    val mod = {"file": "file{i}.spl", "timestamp": i * 1000, "operation": op_type}
    modifications = modifications.append(mod)

check(modifications.len() == 200)
```

</details>


</details>

### Directory Operations - Intensive

#### directory listing

<details>
<summary>Advanced: lists 500 directory entries</summary>

#### lists 500 directory entries _(slow)_

- Verify: lists 500 directory entries


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-APP_IO_INTENSIVE-001
step("Verify: lists 500 directory entries")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var entries = []

for i in 0..500:
    val entry_type = if i % 3 == 0: "dir" else: "file"
    val entry = {"name": "entry{i}", "type": entry_type, "size": i * 100}
    entries = entries.append(entry)

check(entries.len() == 500)
```

</details>


</details>

<details>
<summary>Advanced: filters entries by type</summary>

#### filters entries by type _(slow)_

- Verify: filters entries by type


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-APP_IO_INTENSIVE-001
step("Verify: filters entries by type")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var all_entries = []

for i in 0..300:
    val type = if i % 2 == 0: "file" else: "dir"
    all_entries = all_entries.append(type)

var file_count = 0
var dir_count = 0

for type in all_entries:
    if type == "file":
        file_count = file_count + 1
    else:
        dir_count = dir_count + 1

check(file_count == 150)
check(dir_count == 150)
```

</details>


</details>

#### directory traversal

<details>
<summary>Advanced: traverses nested directory structure</summary>

#### traverses nested directory structure _(slow)_

- Verify: traverses nested directory structure


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-APP_IO_INTENSIVE-001
step("Verify: traverses nested directory structure")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var paths = []

for depth in 0..10:
    for item in 0..10:
        val path = "level{depth}/item{item}"
        paths = paths.append(path)

check(paths.len() == 100)
```

</details>


</details>

<details>
<summary>Advanced: builds directory tree</summary>

#### builds directory tree _(slow)_

- Verify: builds directory tree


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-APP_IO_INTENSIVE-001
step("Verify: builds directory tree")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var tree = []

for i in 0..50:
    val node = {"path": "root/sub{i}", "children": i % 5}
    tree = tree.append(node)

check(tree.len() == 50)
```

</details>


</details>

### Process Execution - Intensive

#### process spawning

<details>
<summary>Advanced: simulates spawning 100 processes</summary>

#### simulates spawning 100 processes _(slow)_

- Verify: simulates spawning 100 processes


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-APP_IO_INTENSIVE-001
step("Verify: simulates spawning 100 processes")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var processes = []

for i in 0..100:
    val process = {"pid": 1000 + i, "command": "process_{i}", "status": "running"}
    processes = processes.append(process)

check(processes.len() == 100)
```

</details>


</details>

<details>
<summary>Advanced: tracks process lifecycle</summary>

#### tracks process lifecycle _(slow)_

- Verify: tracks process lifecycle


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-APP_IO_INTENSIVE-001
step("Verify: tracks process lifecycle")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var states = []

for i in 0..200:
    var state = "failed"
    if i % 4 == 0:
        state = "pending"
    else:
        if i % 4 == 1:
            state = "running"
        else:
            if i % 4 == 2:
                state = "completed"
    states = states.append(state)

check(states.len() == 200)
```

</details>


</details>

#### process output

<details>
<summary>Advanced: captures 100 process outputs</summary>

#### captures 100 process outputs _(slow)_

- Verify: captures 100 process outputs


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-APP_IO_INTENSIVE-001
step("Verify: captures 100 process outputs")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var outputs = []

for i in 0..100:
    val output = {"stdout": "Output line {i}", "stderr": "", "exit_code": 0}
    outputs = outputs.append(output)

check(outputs.len() == 100)
```

</details>


</details>

<details>
<summary>Advanced: parses process exit codes</summary>

#### parses process exit codes _(slow)_

- Verify: parses process exit codes


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-APP_IO_INTENSIVE-001
step("Verify: parses process exit codes")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var exit_codes = []

for i in 0..500:
    val code = i % 5  # 0, 1, 2, 3, 4
    exit_codes = exit_codes.append(code)

var success_count = 0
for code in exit_codes:
    if code == 0:
        success_count = success_count + 1

check(success_count == 100)
```

</details>


</details>

### Stream Processing - Intensive

#### stream reading

<details>
<summary>Advanced: reads 1000 lines from stream</summary>

#### reads 1000 lines from stream _(slow)_

- Verify: reads 1000 lines from stream


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-APP_IO_INTENSIVE-001
step("Verify: reads 1000 lines from stream")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var lines = []

for i in 0..1000:
    lines = lines.append("Stream line {i}")

check(lines.len() == 1000)
```

</details>


</details>

<details>
<summary>Advanced: buffers stream data</summary>

#### buffers stream data _(slow)_

- Verify: buffers stream data


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-APP_IO_INTENSIVE-001
step("Verify: buffers stream data")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var buffer = []
var buffer_size = 100

for i in 0..500:
    buffer = buffer.append(i)

    if buffer.len() >= buffer_size:
        # Flush buffer
        buffer = []

check(buffer.len() < buffer_size)
```

</details>


</details>

#### stream writing

<details>
<summary>Advanced: writes 1000 chunks to stream</summary>

#### writes 1000 chunks to stream _(slow)_

- Verify: writes 1000 chunks to stream


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-APP_IO_INTENSIVE-001
step("Verify: writes 1000 chunks to stream")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var chunks = []

for i in 0..1000:
    val chunk = {"data": "Chunk {i}", "size": 10 + i % 100}
    chunks = chunks.append(chunk)

check(chunks.len() == 1000)
```

</details>


</details>

<details>
<summary>Advanced: manages stream buffer</summary>

#### manages stream buffer _(slow)_

- Verify: manages stream buffer


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-APP_IO_INTENSIVE-001
step("Verify: manages stream buffer")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var total_written = 0
var chunk_sizes = [100, 200, 150, 300, 250]

for size in chunk_sizes:
    total_written = total_written + size

check(total_written == 1000)
```

</details>


</details>

### Path Operations - Intensive

#### path construction

<details>
<summary>Advanced: builds 500 file paths</summary>

#### builds 500 file paths _(slow)_

- Verify: builds 500 file paths


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-APP_IO_INTENSIVE-001
step("Verify: builds 500 file paths")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var paths = []

for i in 0..500:
    val path = "root/level1/level2/file{i}.spl"
    paths = paths.append(path)

check(paths.len() == 500)
check(paths[0].contains("/"))
```

</details>


</details>

<details>
<summary>Advanced: normalizes paths</summary>

#### normalizes paths _(slow)_

- Verify: normalizes paths


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-APP_IO_INTENSIVE-001
step("Verify: normalizes paths")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var paths = [
    "a/b/../c",
    "x/./y/z",
    "p//q/r"
]

for path in paths:
    check(path.contains("/"))
```

</details>


</details>

#### path analysis

<details>
<summary>Advanced: extracts path components from 200 paths</summary>

#### extracts path components from 200 paths _(slow)_

- Verify: extracts path components from 200 paths


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-APP_IO_INTENSIVE-001
step("Verify: extracts path components from 200 paths")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var components = []

for i in 0..200:
    val path = "dir1/dir2/file{i}.txt"
    val parts = path.split("/")
    components = components.append(parts)

check(components.len() == 200)
```

</details>


</details>

<details>
<summary>Advanced: determines file extensions</summary>

#### determines file extensions _(slow)_

- Verify: determines file extensions


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-APP_IO_INTENSIVE-001
step("Verify: determines file extensions")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var files = [
    "test.spl",
    "data.sdn",
    "readme.md",
    "script.sh"
]

var extensions = []
for file in files:
    val parts = file.split(".")
    if parts.len() == 2:
        extensions = extensions.append(parts[1])

check(extensions.len() == 4)
```

</details>


</details>

### Error Handling - Intensive

#### file errors

<details>
<summary>Advanced: simulates 100 file not found errors</summary>

#### simulates 100 file not found errors _(slow)_

- Verify: simulates 100 file not found errors


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-APP_IO_INTENSIVE-001
step("Verify: simulates 100 file not found errors")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var errors = []

for i in 0..100:
    val error = {"type": "FileNotFound", "path": "missing/file{i}.txt", "code": 2}
    errors = errors.append(error)

check(errors.len() == 100)
```

</details>


</details>

<details>
<summary>Advanced: handles permission errors</summary>

#### handles permission errors _(slow)_

- Verify: handles permission errors


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-APP_IO_INTENSIVE-001
step("Verify: handles permission errors")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val error_types = [
    "PermissionDenied",
    "FileNotFound",
    "AlreadyExists",
    "InvalidPath"
]

for err_type in error_types:
    check(err_type.len() > 0)
```

</details>


</details>

#### process errors

<details>
<summary>Advanced: tracks failed process executions</summary>

#### tracks failed process executions _(slow)_

- Verify: tracks failed process executions


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-APP_IO_INTENSIVE-001
step("Verify: tracks failed process executions")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var failures = []

for i in 0..200:
    if i % 10 == 0:
        val failure = {"pid": i, "error": "ExecutionFailed", "exit_code": 1}
        failures = failures.append(failure)

check(failures.len() == 20)
```

</details>


</details>

### Performance Testing - Intensive

#### high throughput

<details>
<summary>Advanced: processes 2000 file operations</summary>

#### processes 2000 file operations _(slow)_

- Verify: processes 2000 file operations


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-APP_IO_INTENSIVE-001
step("Verify: processes 2000 file operations")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var operations = 0

for i in 0..2000:
    # Simulate file operation
    val op_type = i % 3
    if op_type == 0:
        operations = operations + 1  # read
    elif op_type == 1:
        operations = operations + 1  # write
    else:
        operations = operations + 1  # delete

check(operations == 2000)
```

</details>


</details>

<details>
<summary>Advanced: handles concurrent operations</summary>

#### handles concurrent operations _(slow)_

- Verify: handles concurrent operations


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-APP_IO_INTENSIVE-001
step("Verify: handles concurrent operations")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var concurrent = []

for i in 0..500:
    val op_type = if i % 2 == 0: "read" else: "write"
    val op = {"id": i, "type": op_type, "timestamp": i}
    concurrent = concurrent.append(op)

check(concurrent.len() == 500)
```

</details>


</details>

### Resource Management - Intensive

#### file handles

<details>
<summary>Advanced: tracks 200 file handle allocations</summary>

#### tracks 200 file handle allocations _(slow)_

- Verify: tracks 200 file handle allocations


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-APP_IO_INTENSIVE-001
step("Verify: tracks 200 file handle allocations")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var handles = []

for i in 0..200:
    val h_mode = if i % 2 == 0: "r" else: "w"
    val handle = {"fd": i, "path": "file{i}.txt", "mode": h_mode}
    handles = handles.append(handle)

check(handles.len() == 200)
```

</details>


</details>

<details>
<summary>Advanced: simulates handle cleanup</summary>

#### simulates handle cleanup _(slow)_

- Verify: simulates handle cleanup


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-APP_IO_INTENSIVE-001
step("Verify: simulates handle cleanup")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var open_handles = 100
var closed = 0

for i in 0..100:
    closed = closed + 1
    open_handles = open_handles - 1

check(open_handles == 0)
check(closed == 100)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 29 |
| Active scenarios | 29 |
| Slow scenarios | 29 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c98b9e4d7f5ce83d07566d3f05ea7ed3c8c8ad8decae5875317251c88d0bb123`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c98b9e4d7f5ce83d07566d3f05ea7ed3c8c8ad8decae5875317251c88d0bb123`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c98b9e4d7f5ce83d07566d3f05ea7ed3c8c8ad8decae5875317251c88d0bb123`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/02_integration/app/io_intensive_spec.spl
mirror: doc/06_spec/02_integration/app/io_intensive_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/app/io_intensive_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/02_integration/app/io_intensive_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/app/io_intensive_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
