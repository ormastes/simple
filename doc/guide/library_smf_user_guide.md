# Library SMF User Guide

**Version:** 1.0
**Last Updated:** 2026-02-09
**Status:** Production Ready

## Table of Contents

1. [Introduction](#introduction)
2. [Quick Start](#quick-start)
3. [Creating Libraries](#creating-libraries)
4. [Using Libraries](#using-libraries)
5. [Linking Against Libraries](#linking-against-libraries)
6. [Managing Libraries](#managing-libraries)
7. [Best Practices](#best-practices)
8. [Troubleshooting](#troubleshooting)
9. [API Reference](#api-reference)

---

## Introduction

Library SMF (.lsm) is Simple's library archive format for bundling multiple compiled modules into a single file. It provides:

- **Single-file distribution** - Ship one .lsm instead of hundreds of .smf files
- **Fast module loading** - O(1) access via built-in index
- **Integrity verification** - Hash-based validation
- **Native linking support** - Link binaries against library modules

### When to Use Libraries

✅ **Use libraries for:**
- Standard library distribution
- Large applications (>10 modules)
- Plugin systems
- Shared code across projects

❌ **Don't use libraries for:**
- Small scripts (1-3 modules)
- Development/debugging (slower iteration)
- Frequently changing code

---

## Quick Start

### 1. Install Simple

```bash
# Download and install Simple
curl -sSL https://simple-lang.org/install.sh | sh

# Verify installation
simple --version
```

### 2. Create Your First Library

```bash
# Write some modules
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

**Output:**
```
Modules (2):
  - math
  - hello
```

### 3. Use Your Library

```simple
// app.spl
use mylib.math.{add}
use mylib.hello.{greet}

fn main():
    val sum = add(2, 3)
    print("2 + 3 = {sum}")
    greet("World")
```

```bash
# Load library and run
simple run app.spl --libraries=mylib.lsm
```

**Output:**
```
2 + 3 = 5
Hello, World!
```

---

## Creating Libraries

### Method 1: Using lib_tool (Recommended)

Create libraries from existing SMF files:

```bash
# Basic creation
simple scripts/lib_tool.spl create output.lsm module1.smf module2.smf

# With wildcards
simple scripts/lib_tool.spl create libstd.lsm build/smf/*.smf

# Verbose output
simple scripts/lib_tool.spl create mylib.lsm *.smf --verbose
```

### Method 2: Using LibSmfBuilder (Programmatic)

```simple
use compiler.linker.lib_smf_writer.{LibSmfBuilder}

fn main():
    var builder = LibSmfBuilder.new()

    // Add modules from files
    builder.add_module("math/add", "math_add.smf")?
    builder.add_module("math/sub", "math_sub.smf")?

    // Add modules from memory
    val smf_bytes = compile_module_to_smf("string/reverse.spl")?
    builder.add_module_data("string/reverse", smf_bytes)?

    // Write library
    builder.write("mylib.lsm")?

    print("Library created successfully!")
```

### Method 3: Building Standard Library

Build the complete standard library:

```bash
# Compile stdlib
simple scripts/compile_with_objects.spl --input-dir=src/std

# Build library
simple scripts/build_libstd.spl --verbose

# Result: build/lib/libstd.lsm
```

---

## Using Libraries

### Loading Modules at Runtime

```simple
use compiler.loader.module_loader_lib_support.{ModuleLoaderWithLibs}

fn main():
    // Create loader
    var loader = ModuleLoaderWithLibs.new(config)

    // Add library
    loader.add_library("mylib.lsm")?

    // Load module
    val module = loader.load_module("math/operations")?

    // Access module contents
    val header = module.get_header()
    val symbols = module.exported_symbols()

    print("Loaded {symbols.len()} symbols from module")
```

### Configuration Options

```simple
use compiler.loader.module_loader_lib_support.{ModuleLoaderLibConfig}

var config = ModuleLoaderLibConfig.default()

// Enable verbose logging
config.verbose = true

// Enable library support
config.enable_libraries = true

// Set module search paths
config.search_paths = ["./lib", "/usr/lib/simple"]

// Set library search paths
config.library_paths = ["./lib", "/usr/lib/simple"]
```

### Listing Available Modules

```simple
var loader = ModuleLoaderWithLibs.new(config)
loader.add_library("libstd.lsm")?

// List all modules
val modules = loader.list_available_modules()
for module_name in modules:
    print("  - {module_name}")

// Check if module exists
if loader.has_module("std/io/mod"):
    print("Module available!")
```

---

## Linking Against Libraries

### Prerequisites

For native linking, you need both SMF and object files:

```bash
# Compile source to both SMF and object
simple compile module.spl --emit-smf -o module.smf
simple compile module.spl --emit-obj -o module.o

# Or use helper script
simple scripts/compile_with_objects.spl --input-dir=src
```

### Basic Linking

```simple
use compiler.linker.linker_wrapper_lib_support.{link_with_libraries}
use compiler.linker.linker_wrapper.{NativeLinkConfig}

fn main():
    // Configure linking
    var config = NativeLinkConfig.default()
    config.library_paths = ["build/lib", "/usr/lib/simple"]
    config.verbose = true

    // Object files to link
    val objects = ["app/main.o", "app/utils.o"]

    // Link with libraries
    val result = link_with_libraries(objects, "myapp", config)

    match result:
        case Ok(path):
            print("Binary created: {path}")
        case Err(e):
            print("Link error: {e}")
            exit(1)
```

### Advanced Linking Options

```simple
var config = NativeLinkConfig(
    libraries: ["c", "pthread", "m"],      // System libraries
    library_paths: ["build/lib"],          // Library search paths
    runtime_path: "/opt/simple/runtime",   // Runtime library path
    pie: true,                             // Position-independent executable
    debug: true,                           // Include debug info
    verbose: true,                         // Verbose output
    extra_flags: ["-O2", "-flto"]         // Extra linker flags
)
```

### Symbol Resolution

The linker automatically:
1. Scans library paths for .lsm files
2. Extracts undefined symbols from your objects
3. Finds which library modules provide those symbols
4. Locates companion .o files for those modules
5. Links everything together

```bash
# Verbose output shows the process:
[linker-lib] Found 2 libraries
[linker-lib] Found 15 undefined symbols
[linker-lib] Resolved 'simple_print' from libstd:std/io/mod
[object-resolver] Resolved std/io/mod → build/obj/std_io_mod.o
[linker-lib] Linking 8 object files total
```

---

## Managing Libraries

### List Modules

```bash
simple scripts/lib_tool.spl list mylib.lsm
```

**Output:**
```
Listing modules in: mylib.lsm

Modules (5):
  - math/add
  - math/sub
  - string/reverse
  - io/file
  - io/network
```

### Show Library Information

```bash
simple scripts/lib_tool.spl info mylib.lsm
```

**Output:**
```
Library Information
===================
Path: mylib.lsm
Size: 524288 bytes
Format: Library SMF v1.0
Modules: 5

Module List:
  math/add
    Offset: 256
    Size: 4096 bytes
    Hash: 0x1234567890abcdef
  ...
```

### Verify Integrity

```bash
simple scripts/lib_tool.spl verify mylib.lsm
```

**Output:**
```
Verifying library: mylib.lsm

Checking 5 modules...
  ✓ math/add
  ✓ math/sub
  ✓ string/reverse
  ✓ io/file
  ✓ io/network

Results:
  Verified: 5
  Failed: 0

✓ All modules verified
```

### Extract Module

```bash
# Extract to default name
simple scripts/lib_tool.spl extract mylib.lsm math/add

# Extract to custom path
simple scripts/lib_tool.spl extract mylib.lsm math/add --output=my_add.smf
```

---

## Best Practices

### 1. Library Organization

**Group related modules:**
```
libstd.lsm
  ├── std/io/mod
  ├── std/io/file
  ├── std/io/network
  ├── std/collections/list
  └── std/collections/map

libmath.lsm
  ├── math/basic
  ├── math/trig
  └── math/stats
```

**Don't mix unrelated code:**
```
❌ mixed.lsm
  ├── io/file
  ├── math/trig
  └── gui/button  # Unrelated
```

### 2. Versioning

Include version in library name:
```
libstd-1.0.0.lsm
libmath-2.1.0.lsm
```

### 3. Module Naming

Use clear, hierarchical names:
```
✅ Good:
  - std/io/file
  - std/collections/list
  - app/database/connection

❌ Bad:
  - f
  - list1
  - db_conn_v2_final
```

### 4. Build Workflow

```bash
# 1. Compile source to SMF + objects
simple scripts/compile_with_objects.spl --input-dir=src

# 2. Build library
simple scripts/build_libstd.spl

# 3. Verify
simple scripts/lib_tool.spl verify build/lib/libstd.lsm

# 4. Install (optional)
sudo cp build/lib/libstd.lsm /usr/lib/simple/
```

### 5. CI/CD Integration

```yaml
# .github/workflows/build.yml
- name: Build Standard Library
  run: |
    simple scripts/compile_with_objects.spl --input-dir=src/std
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

### Module Not Found

**Error:**
```
Error: Module not found: 'std/io/mod'
```

**Solutions:**
1. Verify library is added:
   ```simple
   loader.add_library("libstd.lsm")?
   ```

2. Check library contains module:
   ```bash
   simple scripts/lib_tool.spl list libstd.lsm | grep "io/mod"
   ```

3. Verify library path:
   ```simple
   config.library_paths = ["build/lib", "/usr/lib/simple"]
   ```

### Object File Not Found

**Error:**
```
Error: Object file not found for module 'std/io/mod'
  Searched in: build/obj, obj, .
  Candidates: std/io/mod.o, std_io_mod.o, mod.o
```

**Solutions:**
1. Compile with objects:
   ```bash
   simple compile std/io/mod.spl --emit-obj -o std_io_mod.o
   ```

2. Use helper script:
   ```bash
   simple scripts/compile_with_objects.spl --input-dir=src/std
   ```

3. Check object location:
   ```bash
   find build/obj -name "*io_mod.o"
   ```

### Hash Verification Failed

**Error:**
```
Error: Hash mismatch for module 'math/add'
  Expected: 0x1234567890abcdef
  Got: 0xfedcba0987654321
```

**Solutions:**
1. Rebuild library:
   ```bash
   simple scripts/build_libstd.spl
   ```

2. Verify SMF file integrity:
   ```bash
   file math_add.smf
   ```

3. Check for corruption:
   ```bash
   simple scripts/lib_tool.spl verify mylib.lsm
   ```

### Undefined Symbol

**Error:**
```
Error: Undefined symbol 'unknown_function'
  Checked 50 modules in 2 libraries
```

**Solutions:**
1. Check symbol is exported:
   ```simple
   export unknown_function
   ```

2. Verify module is compiled:
   ```bash
   simple scripts/lib_tool.spl list mylib.lsm
   ```

3. Check library is in path:
   ```simple
   config.library_paths.push("path/to/lib")
   ```

---

## API Reference

### LibSmfBuilder

Create and build library archives.

```simple
use compiler.linker.lib_smf_writer.{LibSmfBuilder}

var builder = LibSmfBuilder.new()

// Add module from file
builder.add_module(name: text, path: text) -> Result

// Add module from memory
builder.add_module_data(name: text, data: [u8]) -> Result

// Write library to file
builder.write(path: text) -> Result

// Enable verbose output
builder.set_verbose(verbose: bool)
```

### ModuleLoaderWithLibs

Load modules from libraries at runtime.

```simple
use compiler.loader.module_loader_lib_support.{ModuleLoaderWithLibs}

var loader = ModuleLoaderWithLibs.new(config)

// Add library
loader.add_library(path: text) -> Result

// Load module
loader.load_module(name: text) -> Result<SmfReaderMemory>

// Check if module exists
loader.has_module(name: text) -> bool

// List available modules
loader.list_available_modules() -> [text]

// Get module source
loader.get_module_source(name: text) -> Result<text>
```

### link_with_libraries()

Link object files with library support.

```simple
use compiler.linker.linker_wrapper_lib_support.{link_with_libraries}

link_with_libraries(
    object_files: [text],
    output: text,
    config: NativeLinkConfig
) -> Result<text>
```

### NativeLinkConfig

Configuration for native linking.

```simple
use compiler.linker.linker_wrapper.{NativeLinkConfig}

var config = NativeLinkConfig.default()

config.libraries: [text]         // System libraries to link
config.library_paths: [text]     // Paths to search for .lsm files
config.runtime_path: text        // Path to runtime library
config.pie: bool                 // Position-independent executable
config.debug: bool               // Include debug info
config.verbose: bool             // Verbose output
config.extra_flags: [text]       // Extra linker flags
```

---

## Examples

### Example 1: Math Library

**Create:**
```bash
# math/add.spl
fn add(a: i64, b: i64) -> i64: a + b
export add

# math/mul.spl
fn mul(a: i64, b: i64) -> i64: a * b
export mul

# Compile and package
simple compile math/add.spl --emit-smf -o add.smf
simple compile math/mul.spl --emit-smf -o mul.smf
simple scripts/lib_tool.spl create libmath.lsm add.smf mul.smf
```

**Use:**
```simple
use libmath.add.{add}
use libmath.mul.{mul}

fn main():
    val result = add(mul(2, 3), 4)  // (2 * 3) + 4
    print("Result: {result}")
```

### Example 2: Plugin System

**Define plugin interface:**
```simple
// plugin/interface.spl
trait Plugin:
    fn name() -> text
    fn init()
    fn execute()

export Plugin
```

**Load plugins from library:**
```simple
use compiler.loader.module_loader_lib_support.{ModuleLoaderWithLibs}

fn main():
    var loader = ModuleLoaderWithLibs.new(config)
    loader.add_library("plugins.lsm")?

    val plugin_names = ["weather", "news", "stocks"]

    for name in plugin_names:
        val module = loader.load_module("plugins/{name}")?
        print("Loaded plugin: {name}")
        // Initialize and execute plugin
    ```

### Example 3: Distributed Library

**Package for distribution:**
```bash
# Build
simple scripts/compile_with_objects.spl --input-dir=mylib
simple scripts/build_libstd.spl --output=dist/mylib.lsm

# Verify
simple scripts/lib_tool.spl verify dist/mylib.lsm

# Package
tar czf mylib-1.0.0.tar.gz dist/mylib.lsm README.md LICENSE

# Distribute
scp mylib-1.0.0.tar.gz user@server:/packages/
```

**Install:**
```bash
# Download and extract
wget https://example.com/mylib-1.0.0.tar.gz
tar xzf mylib-1.0.0.tar.gz

# Install
sudo cp dist/mylib.lsm /usr/lib/simple/
```

---

## Next Steps

- **Tutorial:** Follow the [Library SMF Tutorial](tutorial.md)
- **Format Spec:** Read the [Format Specification](../format/lib_smf_specification.md)
- **Integration:** See [Integration Guide](../guide/lib_smf_integration.md)
- **API Docs:** Browse the [API Reference](../api/linker.md)

---

**Questions?** Ask on [Discord](https://discord.gg/simple-lang) or [GitHub Discussions](https://github.com/simple-lang/simple/discussions)
