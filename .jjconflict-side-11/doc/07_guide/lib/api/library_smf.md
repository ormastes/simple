# Library SMF Guide

Covers creating, using, and managing Library SMF (.lsm) archives -- Simple's format for bundling multiple compiled modules into a single file.

---

## Overview

Library SMF (.lsm) bundles multiple compiled SMF modules into one file:

- **Single-file distribution** -- ship one .lsm instead of many .smf files
- **O(1) module access** via built-in index
- **Integrity verification** with hash-based validation
- **Native linking support** -- link binaries against library modules

### When to Use

Use libraries for standard library distribution, large applications (>10 modules), plugin systems, and shared code across projects. For small scripts (1-3 modules) or rapidly changing code, individual .smf files are simpler.

---

## Quick Start

### Create a Library

```bash
# Write source modules
mkdir -p mylib
echo 'fn add(a: i64, b: i64) -> i64: a + b' > mylib/math.spl
echo 'fn greet(name: text): print("Hello, {name}!")' > mylib/hello.spl

# Compile to SMF
simple compile mylib/math.spl --emit-smf -o math.smf
simple compile mylib/hello.spl --emit-smf -o hello.smf

# Create library
simple scripts/lib_tool.spl create mylib.lsm math.smf hello.smf

# Verify
simple scripts/lib_tool.spl list mylib.lsm
```

### Use a Library

```simple
use mylib.math.{add}
use mylib.hello.{greet}

fn main():
    print "2 + 3 = {add(2, 3)}"
    greet("World")
```

```bash
simple run app.spl --libraries=mylib.lsm
```

---

## Creating Libraries

### Using lib_tool (Recommended)

```bash
simple scripts/lib_tool.spl create output.lsm module1.smf module2.smf
simple scripts/lib_tool.spl create libstd.lsm build/smf/*.smf
```

### Programmatic (LibSmfBuilder)

```simple
use compiler.linker.lib_smf_writer.{LibSmfBuilder}

var builder = LibSmfBuilder.new()
builder.add_module("math/add", "math_add.smf")?
builder.add_module("math/sub", "math_sub.smf")?

# Add from memory
val smf_bytes = compile_module_to_smf("string/reverse.spl")?
builder.add_module_data("string/reverse", smf_bytes)?

builder.write("mylib.lsm")?
```

### Building the Standard Library

```bash
simple scripts/compile_with_objects.spl --input-dir=src/lib
simple scripts/build_libstd.spl --verbose
# Result: build/lib/libstd.lsm
```

---

## Using Libraries

### Loading Modules at Runtime

```simple
use compiler.loader.module_loader_lib_support.{ModuleLoaderWithLibs}

var loader = ModuleLoaderWithLibs.new(config)
loader.add_library("mylib.lsm")?

val module = loader.load_module("math/operations")?
val symbols = module.exported_symbols()

# Check availability
if loader.has_module("std/io/mod"):
    print "Module available!"

# List all modules
val modules = loader.list_available_modules()
```

### SmfGetter (Unified Interface)

`SmfGetter` provides transparent access to both single SMF files and library archives:

```simple
use compiler.linker.smf_getter.{SmfGetter, create_standard_getter}

var getter = create_standard_getter()
getter.add_search_path("/usr/lib/simple")
getter.add_library("/usr/lib/simple/libstd.lsm")

val smf_data = getter.get("std/io/mod")?
val exists = getter.has_module("std/collections/list")
val all = getter.list_modules()
```

---

## Linking Against Libraries

For native linking, you need both SMF and object files:

```bash
# Compile to both formats
simple compile module.spl --emit-smf -o module.smf
simple compile module.spl --emit-obj -o module.o

# Or compile entire directory
simple scripts/compile_with_objects.spl --input-dir=src
```

### Link with Libraries

```simple
use compiler.linker.linker_wrapper_lib_support.{link_with_libraries}
use compiler.linker.linker_wrapper.{NativeLinkConfig}

var config = NativeLinkConfig.default()
config.library_paths = ["build/lib", "/usr/lib/simple"]
config.verbose = true

val result = link_with_libraries(["app/main.o"], "myapp", config)
```

### Fixed Backend Validation

When you want linker/provider resolution to reject backend-mismatched or non-PIC SMF modules instead of using soft fallback behavior, enable the fixed backend flag:

```bash
simple build app.spl --fixed-be
simple build app.spl --fixed-be=llvm
```

Behavior:

- `--fixed-be` aliases to the LLVM validation path.
- ObjectProvider requires matching compile-options metadata and PIC-safe SMF materialization for strict backend mode.
- Library linking through `.lsm` uses the same provider policy as direct `.smf` inputs.

### Symbol Resolution Process

1. Scans library paths for .lsm files
2. Extracts undefined symbols from your object files
3. Finds which library modules provide those symbols
4. Requests embedded object bytes first; if absent, it can materialize temporary objects from exported code units
5. In fixed-backend mode, rejects modules that cannot prove compatible backend/PIC metadata
6. Links everything together

---

## Managing Libraries

### List Modules

```bash
simple scripts/lib_tool.spl list mylib.lsm
```

### Show Information

```bash
simple scripts/lib_tool.spl info mylib.lsm
```

Output includes path, size, format version, module count, and per-module offset/size/hash.

### Verify Integrity

```bash
simple scripts/lib_tool.spl verify mylib.lsm
```

### Extract a Module

```bash
simple scripts/lib_tool.spl extract mylib.lsm math/add
simple scripts/lib_tool.spl extract mylib.lsm math/add --output=my_add.smf
```

---

## Best Practices

### Library Organization

Group related modules together:

```
libstd.lsm
  std/io/mod, std/io/file, std/io/network
  std/collections/list, std/collections/map

libmath.lsm
  math/basic, math/trig, math/stats
```

### Module Naming

Use clear, hierarchical names:

```
std/io/file           # Hierarchical, clear
std/collections/list  # Grouped by domain
app/database/conn     # Application-specific
```

### Build Workflow

```bash
# 1. Compile source to SMF + objects
simple scripts/compile_with_objects.spl --input-dir=src

# 2. Build library
simple scripts/build_libstd.spl

# 3. Verify
simple scripts/lib_tool.spl verify build/lib/libstd.lsm

# 4. Install
sudo cp build/lib/libstd.lsm /usr/lib/simple/
```

### CI/CD

```yaml
- name: Build Standard Library
  run: |
    simple scripts/compile_with_objects.spl --input-dir=src/lib
    simple scripts/build_libstd.spl
    simple scripts/lib_tool.spl verify build/lib/libstd.lsm

- name: Upload Library
  uses: actions/upload-artifact@v3
  with:
    name: libstd
    path: build/lib/libstd.lsm
```

---

## Troubleshooting

| Error | Solution |
|-------|----------|
| `Module not found: 'X'` | Verify library contains module with `lib_tool.spl list`. Check library path. |
| `Object file not found for module 'X'` | Compile with `--emit-obj`. Use `compile_with_objects.spl`. |
| `Hash mismatch for module 'X'` | Rebuild library. Verify source SMF files are not corrupted. |
| `Undefined symbol 'X'` | Ensure function is exported (`export fn_name`). Verify module is in library. |

---

## API Reference

### LibSmfBuilder

```simple
var builder = LibSmfBuilder.new()
builder.add_module(name: text, path: text) -> Result
builder.add_module_data(name: text, data: [u8]) -> Result
builder.write(path: text) -> Result
builder.set_verbose(verbose: bool)
```

### ModuleLoaderWithLibs

```simple
var loader = ModuleLoaderWithLibs.new(config)
loader.add_library(path: text) -> Result
loader.load_module(name: text) -> Result<SmfReaderMemory>
loader.has_module(name: text) -> bool
loader.list_available_modules() -> [text]
```

### link_with_libraries

```simple
link_with_libraries(
    object_files: [text],
    output: text,
    config: NativeLinkConfig
) -> Result<text>
```

### NativeLinkConfig

```simple
var config = NativeLinkConfig.default()
config.libraries: [text]         # System libraries to link
config.library_paths: [text]     # Paths to search for .lsm files
config.runtime_path: text        # Runtime library path
config.pie: bool                 # Position-independent executable
config.debug: bool               # Include debug info
config.verbose: bool             # Verbose output
config.extra_flags: [text]       # Extra linker flags
```

---

## Related Files

- lib_tool script: `scripts/lib_tool.spl`
- LibSmfBuilder: `src/compiler/70.backend/linker/lib_smf_writer.spl`
- LibSmfReader: `src/compiler/70.backend/linker/lib_smf_reader.spl`
- SmfGetter: `src/compiler/70.backend/linker/smf_getter.spl`
- Build script: `scripts/build_libstd.spl`
- Compile script: `scripts/compile_with_objects.spl`
