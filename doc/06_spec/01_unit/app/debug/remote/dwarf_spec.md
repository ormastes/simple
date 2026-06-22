# Dwarf Specification

> <details>

<!-- sdn-diagram:id=dwarf_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dwarf_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dwarf_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dwarf_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 27 | 27 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dwarf Specification

## Scenarios

### SourceLocation

### creation with at()

#### creates a location with file, line, and column

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val loc = SourceLocation.at("main.spl", 42, 10)
expect(loc.file).to_equal("main.spl")
expect(loc.line).to_equal(42)
expect(loc.column).to_equal(10)
```

</details>

#### creates a location with column 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val loc = SourceLocation.at("test.spl", 1, 0)
expect(loc.column).to_equal(0)
```

</details>

#### creates a location with large line number

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val loc = SourceLocation.at("big.spl", 99999, 5)
expect(loc.line).to_equal(99999)
```

</details>

### creation with at_line()

#### creates a location with column defaulting to 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val loc = SourceLocation.at_line("main.spl", 42)
expect(loc.file).to_equal("main.spl")
expect(loc.line).to_equal(42)
expect(loc.column).to_equal(0)
```

</details>

#### creates a location with line 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val loc = SourceLocation.at_line("start.spl", 1)
expect(loc.line).to_equal(1)
```

</details>

### to_string()

#### formats with column when column > 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val loc = SourceLocation.at("main.spl", 42, 10)
expect(loc.to_string()).to_equal("main.spl:42:10")
```

</details>

#### formats without column when column is 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val loc = SourceLocation.at_line("main.spl", 42)
expect(loc.to_string()).to_equal("main.spl:42")
```

</details>

#### includes full path in output

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val loc = SourceLocation.at("/home/user/src/main.spl", 10, 5)
expect(loc.to_string()).to_equal("/home/user/src/main.spl:10:5")
```

</details>

#### formats at_line result without column

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val loc = SourceLocation.at_line("test.spl", 100)
expect(loc.to_string()).to_equal("test.spl:100")
```

</details>

### is_valid()

#### returns true for valid location

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val loc = SourceLocation.at("main.spl", 1, 0)
expect(loc.is_valid()).to_equal(true)
```

</details>

#### returns false for empty file

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val loc = SourceLocation.at("", 1, 0)
expect(loc.is_valid()).to_equal(false)
```

</details>

#### returns false for line 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val loc = SourceLocation.at("main.spl", 0, 0)
expect(loc.is_valid()).to_equal(false)
```

</details>

#### returns false for negative line

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val loc = SourceLocation.at("main.spl", -1, 0)
expect(loc.is_valid()).to_equal(false)
```

</details>

#### returns false for empty file and line 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val loc = SourceLocation.at("", 0, 0)
expect(loc.is_valid()).to_equal(false)
```

</details>

### field access

#### accesses file field directly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val loc = SourceLocation.at("src/app.spl", 25, 3)
expect(loc.file).to_equal("src/app.spl")
```

</details>

#### accesses line field directly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val loc = SourceLocation.at("test.spl", 50, 1)
expect(loc.line).to_equal(50)
```

</details>

#### accesses column field directly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val loc = SourceLocation.at("test.spl", 50, 7)
expect(loc.column).to_equal(7)
```

</details>

### DwarfInfo

### construction

#### creates an unloaded DwarfInfo

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val info = DwarfInfo.create_unloaded("/path/to/binary")
expect(info.handle).to_equal(0)
expect(info.binary_path).to_equal("/path/to/binary")
expect(info.loaded).to_equal(false)
```

</details>

#### creates a loaded DwarfInfo with handle

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val info = DwarfInfo.create_loaded(42, "/path/to/binary")
expect(info.handle).to_equal(42)
expect(info.loaded).to_equal(true)
```

</details>

### is_loaded()

#### returns false for unloaded info

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val info = DwarfInfo.create_unloaded("/path/to/binary")
expect(info.is_loaded()).to_equal(false)
```

</details>

#### returns true for loaded info with valid handle

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val info = DwarfInfo.create_loaded(1, "/path/to/binary")
expect(info.is_loaded()).to_equal(true)
```

</details>

#### returns false when handle is 0 even if loaded flag is true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val info = DwarfInfo(handle: 0, binary_path: "test", loaded: true)
expect(info.is_loaded()).to_equal(false)
```

</details>

### get_binary_path()

#### returns the binary path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val info = DwarfInfo.create_unloaded("/usr/bin/myapp")
expect(info.get_binary_path()).to_equal("/usr/bin/myapp")
```

</details>

#### returns empty string for empty path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val info = DwarfInfo.create_unloaded("")
expect(info.get_binary_path()).to_equal("")
```

</details>

### close()

#### marks info as unloaded after close

1. var info = DwarfInfo create loaded
2. info close
   - Expected: info.loaded is false
   - Expected: info.handle equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var info = DwarfInfo.create_loaded(42, "/path/to/binary")
info.close()
expect(info.loaded).to_equal(false)
expect(info.handle).to_equal(0)
```

</details>

#### is_loaded returns false after close

1. var info = DwarfInfo create loaded
2. info close
   - Expected: info.is_loaded() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var info = DwarfInfo.create_loaded(99, "/path/to/binary")
info.close()
expect(info.is_loaded()).to_equal(false)
```

</details>

#### close on unloaded info is a no-op

1. var info = DwarfInfo create unloaded
2. info close
   - Expected: info.loaded is false
   - Expected: info.handle equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var info = DwarfInfo.create_unloaded("/path/to/binary")
info.close()
expect(info.loaded).to_equal(false)
expect(info.handle).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/debug/remote/dwarf_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SourceLocation
- creation with at()
- creation with at_line()
- to_string()
- is_valid()
- field access
- DwarfInfo
- construction
- is_loaded()
- get_binary_path()
- close()

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 27 |
| Active scenarios | 27 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
