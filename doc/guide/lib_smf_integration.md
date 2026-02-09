# Library SMF Integration Guide

This guide shows how to integrate Library SMF support into the module loader, linker wrapper, and interpreter.

## Overview

The Library SMF system provides three key components:

1. **LibSmfBuilder/LibSmfWriter** - Create library archives
2. **LibSmfReader** - Read modules from archives
3. **SmfGetter** - Unified interface (single files + libraries)

**Key Principle:** Use `SmfGetter` everywhere instead of directly opening SMF files. This provides transparent access to both single files and library archives.

## Module Loader Integration

### Before: Direct File Access

```simple
# Old code in module_loader.spl
fn load_module(path: text) -> Result<LoadedModule, text>:
    # Direct SMF file access
    val reader = SmfReaderImpl.open(path)?

    # Load symbols
    val symbols = reader.exported_symbols()

    Ok(LoadedModule(
        path: path,
        reader: reader,
        symbols: symbols,
        ...
    ))
```

### After: Using SmfGetter

```simple
# New code in module_loader.spl
use compiler.linker.smf_getter.{SmfGetter, create_standard_getter}

struct ModuleLoader:
    smf_getter: SmfGetter
    ...

impl ModuleLoader:
    static fn new() -> ModuleLoader:
        var getter = create_standard_getter()

        # Add system library directories
        getter.add_search_path("/usr/lib/simple")
        getter.add_search_path("/usr/local/lib/simple")

        # Add standard libraries
        var _ = getter.add_library("/usr/lib/simple/libstd.lsm")

        ModuleLoader(
            smf_getter: getter,
            ...
        )

    fn load_module(module_name: text) -> Result<LoadedModule, text>:
        # Get SMF data from getter (handles both files and libraries)
        val smf_data = self.smf_getter.get(module_name)?

        # Create reader from data
        # TODO: Implement SmfReaderImpl.from_data()
        val reader = create_reader_from_data(smf_data)?

        # Load symbols
        val symbols = reader.exported_symbols()

        Ok(LoadedModule(
            path: module_name,
            reader: reader,
            symbols: symbols,
            ...
        ))

    fn has_module(module_name: text) -> bool:
        self.smf_getter.has_module(module_name)

    fn list_available_modules() -> [text]:
        self.smf_getter.list_modules()
```

## Linker Wrapper Integration

### Before: Link Against Individual Files

```simple
# Old code in linker_wrapper.spl
fn link_to_native(object_files: [text], output: text, config: NativeLinkConfig) -> Result:
    # Build linker command with explicit library paths
    var args: [text] = []
    args = args + (object_files)

    for lib_path in config.library_paths:
        args.push("-L{lib_path}")

    # Link
    execute_linker(args)
```

### After: Support Library SMF

```simple
# New code in linker_wrapper.spl
use compiler.linker.smf_getter.{SmfGetter}

struct LinkContext:
    smf_getter: SmfGetter
    ...

fn link_to_native(object_files: [text], output: text, config: NativeLinkConfig) -> Result:
    # Setup SMF getter
    var getter = SmfGetter.new()

    # Add library search paths
    for lib_path in config.library_paths:
        getter.add_search_path(lib_path)

    # Scan for .lsm libraries
    var _ = scan_and_add_libraries(getter, config.library_paths)

    # Resolve dependencies from libraries
    val resolved_deps = resolve_dependencies(object_files, getter)?

    # Build linker command
    var args: [text] = []
    args = args + (object_files)
    args = args + (resolved_deps)

    # Link
    execute_linker(args)

fn scan_and_add_libraries(getter: SmfGetter, paths: [text]) -> Result<(), text>:
    """Scan paths for .lsm files and add them to getter."""
    for path in paths:
        # TODO: List directory for *.lsm files
        # For each library file:
        var _ = getter.add_library("{path}/libstd.lsm")
        var _ = getter.add_library("{path}/libstd_io.lsm")

    Ok(())

fn resolve_dependencies(object_files: [text], getter: SmfGetter) -> Result<[text], text>:
    """Resolve module dependencies from libraries."""
    var resolved: [text] = []

    # TODO: Parse object files for undefined symbols
    # Look up symbols in getter
    # Extract needed SMF modules
    # Return list of resolved module files

    Ok(resolved)
```

## Interpreter Integration

### Before: Load Single SMF Files

```simple
# Old interpreter code
fn load_runtime_module(name: text) -> Result:
    val smf_path = "{runtime_dir}/{name}.smf"
    val reader = SmfReaderImpl.open(smf_path)?

    # Execute module
    execute_smf(reader)
```

### After: Load from Libraries

```simple
# New interpreter code
use compiler.linker.smf_getter.{SmfGetter}

struct Interpreter:
    smf_getter: SmfGetter
    ...

impl Interpreter:
    static fn new() -> Interpreter:
        var getter = SmfGetter.new()

        # Add interpreter runtime libraries
        val runtime_dir = env_get("SIMPLE_RUNTIME_DIR") ?? "/usr/lib/simple"
        getter.add_search_path(runtime_dir)

        # Load standard library archive
        var _ = getter.add_library("{runtime_dir}/libstd.lsm")

        Interpreter(
            smf_getter: getter,
            ...
        )

    fn load_runtime_module(name: text) -> Result:
        # Get from getter (transparently handles libraries)
        val smf_data = self.smf_getter.get(name)?

        # Create reader
        val reader = create_reader_from_data(smf_data)?

        # Execute module
        execute_smf(reader)

    fn import_module(module_path: text) -> Result:
        # Check if available
        if not self.smf_getter.has_module(module_path):
            return Err("Module not found: {module_path}")

        # Load and execute
        self.load_runtime_module(module_path)
```

## Building Standard Library Archives

### Build Script Example

```simple
#!/usr/bin/env simple
use compiler.linker.lib_smf_writer.{LibSmfBuilder}

fn main():
    # Create standard library archive
    var builder = LibSmfBuilder.new()
    builder.set_verbose(true)

    # Add I/O modules
    builder.add_module("std/io/mod", "build/smf/std/io/mod.smf")
    builder.add_module("std/io/file", "build/smf/std/io/file.smf")
    builder.add_module("std/io/dir", "build/smf/std/io/dir.smf")

    # Add collections modules
    builder.add_module("std/collections/list", "build/smf/std/collections/list.smf")
    builder.add_module("std/collections/dict", "build/smf/std/collections/dict.smf")

    # Write library
    val result = builder.write("build/lib/libstd.lsm")
    if result.is_err():
        print "Error: {result.unwrap_err()}"
        exit(1)

    print "Created libstd.lsm with {builder.module_count()} modules"
```

### Makefile Integration

```makefile
# Build individual SMF files
build/smf/std/io/mod.smf: src/std/io/mod.spl
    simple compile $< -o $@

# Build library archive
build/lib/libstd.lsm: $(STD_SMF_FILES)
    ./script/build-stdlib-archive.spl

# Install libraries
install: build/lib/libstd.lsm
    install -D build/lib/libstd.lsm /usr/lib/simple/libstd.lsm
```

## Testing Integration

### Test Library Loading

```simple
describe "SmfGetter with libraries":
    before_each:
        # Create test library
        var builder = LibSmfBuilder.new()
        builder.add_module("test/mod1", create_test_smf("mod1"))
        builder.add_module("test/mod2", create_test_smf("mod2"))
        builder.write("test.lsm")

    after_each:
        file_delete("test.lsm")

    it "loads modules from library":
        var getter = SmfGetter.new()
        getter.add_library("test.lsm")

        expect(getter.has_module("test/mod1")).to_equal(true)

        val data = getter.get("test/mod1")
        expect(data.is_ok()).to_equal(true)

    it "prefers library over single files":
        # Create both library and single file with same name
        file_write("test_mod1.smf", create_test_smf("single"))
        var builder = LibSmfBuilder.new()
        builder.add_module("test/mod1", create_test_smf("library"))
        builder.write("test.lsm")

        var getter = SmfGetter.new()
        getter.add_search_path(".")
        getter.add_library("test.lsm")

        # Should load from library (indexed first)
        val data = getter.get("test/mod1")
        # Verify it's the library version
```

## Migration Path

### Phase 1: Add Library Support (Current)

- ✅ Implement library SMF format
- ✅ Create LibSmfBuilder, LibSmfReader
- ✅ Create SmfGetter abstraction
- ✅ Write tests and documentation

### Phase 2: Integrate with Loader

- [ ] Update ModuleLoader to use SmfGetter
- [ ] Add SmfReaderImpl.from_data() method
- [ ] Update module cache to track source type
- [ ] Test module loading from libraries

### Phase 3: Integrate with Linker

- [ ] Update linker wrapper to scan for .lsm files
- [ ] Add dependency resolution from libraries
- [ ] Support linking against library modules
- [ ] Test native linking with libraries

### Phase 4: Integrate with Interpreter

- [ ] Update interpreter to use SmfGetter
- [ ] Load runtime modules from libraries
- [ ] Support dynamic imports from libraries
- [ ] Test interpreter execution

### Phase 5: Build System Integration

- [ ] Create build scripts for standard library
- [ ] Generate libstd.lsm during build
- [ ] Install libraries to system paths
- [ ] Update package manager support

### Phase 6: Optimization

- [ ] Add compression support
- [ ] Implement memory-mapped loading
- [ ] Add hash-based module lookup
- [ ] Profile and optimize performance

## Best Practices

### Library Organization

**Good:**
```
libstd.lsm          # Complete standard library
libstd_io.lsm       # I/O subsystem only
libstd_net.lsm      # Networking only
libapp.lsm          # Application-specific modules
```

**Bad:**
```
lib1.lsm            # Unclear purpose
std_and_app.lsm     # Mixed standard and app modules
```

### Module Naming

**Good:**
```
std/io/mod           # Hierarchical, clear
std/collections/list
app/ui/button
```

**Bad:**
```
stdio                # Ambiguous
list                 # Too generic, collisions likely
mod                  # No context
```

### Error Handling

**Always verify:**
- Library magic number
- Module hash integrity
- File boundaries
- Version compatibility

**Example:**
```simple
fn load_with_verification(getter: SmfGetter, name: text) -> Result:
    # Check existence first
    if not getter.has_module(name):
        return Err("Module not found: {name}")

    # Get data (automatically verifies hash)
    val data = getter.get(name)?

    # Additional validation
    if data.len() < 128:
        return Err("Invalid SMF data for {name}")

    Ok(data)
```

### Performance Tips

1. **Cache library readers** - SmfGetter caches LibSmfReader instances
2. **Batch module loads** - Load multiple modules in one pass
3. **Lazy library loading** - Only add libraries when needed
4. **Profile module access** - Identify frequently accessed modules

## Troubleshooting

### Module Not Found

```
Error: Module not found: std/io/mod
```

**Solutions:**
- Check module name matches exactly (case-sensitive)
- Verify library contains module: `simple lib list library.lsm`
- Ensure library is added to getter: `getter.add_library(path)`
- Check search paths: `getter.add_search_path(path)`

### Hash Mismatch

```
Error: Hash mismatch for module std/io/mod
```

**Solutions:**
- Library may be corrupted - regenerate it
- Module may have been modified externally
- Verify library integrity: `simple lib verify library.lsm`

### Performance Issues

**Symptoms:** Slow module loading

**Solutions:**
- Check if libraries are being reopened repeatedly
- Ensure SmfGetter instance is reused
- Profile with `SIMPLE_PROFILE=1`
- Consider memory-mapping for large libraries

## Examples

See also:
- `src/compiler/linker/test/lib_smf_spec.spl` - Complete test suite
- `examples/lib_smf/` - Example usage scripts
- `script/build-stdlib-archive.spl` - Build standard library

---

**Next Steps:**
1. Implement SmfReaderImpl.from_data()
2. Update ModuleLoader to use SmfGetter
3. Create build script for libstd.lsm
4. Test end-to-end module loading
