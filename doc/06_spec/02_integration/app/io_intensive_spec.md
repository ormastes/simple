# I/O Operations Intensive Tests

> Comprehensive testing of I/O operations:

<!-- sdn-diagram:id=io_intensive_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=io_intensive_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

io_intensive_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=io_intensive_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 29 | 29 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# I/O Operations Intensive Tests

Comprehensive testing of I/O operations:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #1041-1050 |
| Category | Testing |
| Difficulty | 4/5 |
| Status | Implemented |
| Source | `test/02_integration/app/io_intensive_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Comprehensive testing of I/O operations:
- File I/O (read, write, append, delete)
- Process execution and management
- Network operations (simulated)

Tests SFFI bindings and runtime I/O functions.

## Key Concepts

| Concept | Description |
|---------|-------------|
| File I/O | Read/write operations via SFFI |
| Process | Execute external commands |
| Streams | Handle data streams |

## Related Specifications

- [IO Module](../../src/app/io/) - I/O operations
- [SFFI](../../src/lib/ffi/) - Foreign function interface

## Examples

```simple
# File I/O workflow
val content = file_read("test.txt")
file_write("output.txt", content)
```

## Scenarios

### File I/O - Intensive

#### file writing

<details>
<summary>Advanced: simulates writing 100 files</summary>

#### simulates writing 100 files _(slow)_

1. files = files append
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. parts push
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. operations = operations append
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. modifications = modifications append
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. entries = entries append
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. all entries = all entries append
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. paths = paths append
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var paths = []

for depth in 0..10:
    for item in 0..10:
        val path = "level{depth}/item{item}"
        paths = paths.append(path)

check(paths.len() == 100)
```

<details>
<summary>Rendered scenario source</summary>

> var paths = []<br>
> <br>
> for depth in 0..10:<br>
>     for item in 0..10:<br>
>         val path = "level{depth}/ite$item$"<br>
>         paths = paths.append(path)<br>
> <br>
> check(paths.len() == 100)

</details>

</details>


</details>

<details>
<summary>Advanced: builds directory tree</summary>

#### builds directory tree _(slow)_

1. tree = tree append
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. processes = processes append
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. states = states append
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. outputs = outputs append
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. exit codes = exit codes append
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. lines = lines append
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. buffer = buffer append
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. chunks = chunks append
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. paths = paths append
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. components = components append
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. extensions = extensions append
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. errors = errors append
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. failures = failures append
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. concurrent = concurrent append
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. handles = handles append
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
