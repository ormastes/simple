# SMF to Object File Conversion - Design Challenge

**Date:** 2026-02-09
**Status:** Design Proposal
**Context:** Library SMF Phase 3 (Linker Integration) blocker

## Problem Statement

The linker wrapper needs to link native object files (.o) with modules from library archives (.lsm). The challenge is converting SMF (Simple Module Format) modules to object files that the native linker (ld, mold, lld) can process.

**Current Situation:**
```
Library (.lsm) → Extract Module → SMF bytes → ??? → Object file (.o) → Native Linker
                                              BLOCKED
```

## Understanding SMF Format

**SMF (Simple Module Format)** is a binary format containing:
- Header (128 bytes) - metadata, version, platform, flags
- Sections - code, data, rodata, symbols, etc.
- Symbol table - exported/imported symbols with offsets
- String table - symbol names

**Key Insight:** SMF sections may contain:
1. **Machine code** (x86_64/aarch64/riscv64 instructions)
2. **JIT-compiled code** (Cranelift output)
3. **Bytecode** (interpreter format)
4. **Mixed formats** (depending on compilation mode)

## The Core Challenge

### Challenge 1: SMF is Not Source

SMF is a compiled artifact. Unlike source code, we cannot simply "recompile" it. We need to either:
- Extract and repackage existing machine code
- Reconstruct intermediate representation (MIR) and recompile

### Challenge 2: Object File Format Differences

Native linkers expect specific formats:
- **Linux:** ELF (Executable and Linkable Format)
- **macOS:** Mach-O
- **Windows:** COFF/PE

SMF is Simple's custom format, not directly compatible.

### Challenge 3: Relocation Information

Object files contain relocation entries for:
- Function calls to external symbols
- Global variable references
- Position-independent code (PIC)

SMF may not preserve all necessary relocation information.

## Proposed Solutions

### Solution 1: SMF to ELF Wrapper (Simplest)

**Approach:** Create ELF object files that wrap SMF machine code sections.

**Implementation:**
```simple
fn smf_to_object_simple(smf_data: [u8], output: text) -> Result:
    # 1. Parse SMF
    val reader = SmfReaderMemory.from_data(smf_data)?
    val header = reader.get_header()

    # 2. Extract code sections
    # (Assuming SMF has machine code in .text-like sections)
    val code_sections = extract_code_sections(reader)?

    # 3. Build ELF header
    var elf = ElfBuilder.new(header.arch, header.platform)

    # 4. Add sections
    for section in code_sections:
        elf.add_section(section.name, section.data, section.flags)

    # 5. Add symbols
    val symbols = reader.exported_symbols()
    for sym in symbols:
        elf.add_symbol(sym.name, sym.offset, sym.size, sym.binding)

    # 6. Write ELF file
    elf.write(output)?
    Ok(())
```

**Pros:**
- ✅ Direct machine code reuse
- ✅ No recompilation needed
- ✅ Fast conversion (~10ms per module)

**Cons:**
- ❌ Requires ELF library or builder
- ❌ May lose relocation information
- ❌ Platform-specific (need Mach-O, COFF variants)

**Estimated Effort:** 2-3 days

### Solution 2: MIR Reconstruction and Recompilation (Most Robust)

**Approach:** Extend SMF to store MIR, then recompile to object files.

**Implementation:**
```simple
fn smf_to_object_recompile(smf_data: [u8], output: text, config: CodegenConfig) -> Result:
    # 1. Parse SMF and extract MIR section
    val reader = SmfReaderMemory.from_data(smf_data)?
    val mir_section = reader.get_section_by_type(SectionType.MirData)?

    # 2. Deserialize MIR
    val mir_module = MirModule.deserialize(mir_section.data)?

    # 3. Create AOT codegen pipeline
    val pipeline = CodegenPipeline.aot(config.target)

    # 4. Compile MIR to object file
    val compiled = pipeline.compile_module(mir_module)?
    compiled.emit_object(output)?
    compiled.cleanup()

    Ok(())
```

**Pros:**
- ✅ Proper relocation information
- ✅ Platform-independent approach
- ✅ Full optimization pipeline available
- ✅ Type-safe compilation

**Cons:**
- ❌ Requires MIR storage in SMF (format change)
- ❌ Slower conversion (~100-500ms per module)
- ❌ Larger SMF files (stores both code + MIR)

**Estimated Effort:** 1-2 weeks

### Solution 3: Hybrid - Pre-Generate Object Files (Pragmatic)

**Approach:** Generate both .smf and .o files during compilation, store .o in library.

**Implementation:**
```simple
# Build process change:
fn compile_module(source: text, output_smf: text):
    # Current: Only generate SMF
    val compiled = compile_to_smf(source)?
    write_file(output_smf, compiled)

    # NEW: Also generate object file
    val obj_path = output_smf.replace(".smf", ".o")
    val obj_compiled = compile_to_object(source)?
    write_file(obj_path, obj_compiled)

    # Store both in library
    builder.add_module_with_object("mod_name", output_smf, obj_path)
```

**Library Format Change:**
```
Library (.lsm) contains:
  - Module index
  - SMF data (for module loading/interpretation)
  - Object files (for native linking)
```

**Pros:**
- ✅ No conversion needed at link time
- ✅ Fast linking
- ✅ Works with existing tools
- ✅ No format changes to SMF

**Cons:**
- ❌ Larger library files (2x size)
- ❌ Requires separate compilation pipeline
- ❌ Storage overhead

**Estimated Effort:** 2-4 days

### Solution 4: Direct SMF Linking (Experimental)

**Approach:** Teach the linker to understand SMF format directly.

**Implementation:**
- Create ld plugin or wrapper
- Parse SMF and extract symbols
- Link SMF sections directly

**Pros:**
- ✅ No conversion needed
- ✅ Unified format

**Cons:**
- ❌ Complex linker integration
- ❌ May not work with all linkers
- ❌ Platform-specific plugins

**Estimated Effort:** 2-3 weeks

## Recommendation

**Short Term (Now):** **Solution 3 - Hybrid Pre-Generation**

**Rationale:**
1. **Minimal risk** - Uses existing compilation pipeline
2. **Fast to implement** - 2-4 days
3. **Works immediately** - No format changes
4. **Storage acceptable** - stdlib ~1MB → ~2MB

**Long Term (v1.0):** **Solution 2 - MIR Reconstruction**

**Rationale:**
1. **Clean architecture** - Single source of truth (MIR)
2. **Flexible** - Can target any platform at link time
3. **Optimizable** - Link-time optimization possible

## Implementation Plan - Solution 3

### Phase 3a: Pre-Generate Object Files (2 days)

**Step 1: Extend SMF Builder**
```simple
# In lib_smf_writer.spl
me add_module_with_object(
    name: text,
    smf_path: text,
    obj_path: text
) -> Result:
    # Store both SMF and object data
    val smf_data = file_read_bytes(smf_path)?
    val obj_data = file_read_bytes(obj_path)?

    # Add entry with both
    self.entries.push(LibSmfEntryExtended(
        name: name,
        smf_data: smf_data,
        obj_data: obj_data,
        ...
    ))
```

**Step 2: Update Build Process**
```simple
# In scripts/build_libstd.spl
for smf_path in smf_files:
    val module_name = derive_module_name(smf_path)
    val obj_path = smf_path.replace(".smf", ".o")

    if file_exists(obj_path):
        builder.add_module_with_object(module_name, smf_path, obj_path)
    else:
        # Fallback: just SMF
        builder.add_module(module_name, smf_path)
```

**Step 3: Extract Objects During Linking**
```simple
# In linker_wrapper_lib_support.spl
fn extract_objects_from_library(
    library_path: text,
    module_names: [text]
) -> Result<[text], text>:
    var object_paths: [text] = []

    for module_name in module_names:
        val obj_data = library.get_module_object(module_name)?
        val temp_path = "/tmp/lib_{module_name}.o"
        write_bytes_to_file(temp_path, obj_data)?
        object_paths.push(temp_path)

    Ok(object_paths)
```

**Step 4: Complete link_with_libraries()**
```simple
# Replace TODO with actual implementation
for resolved_mod in resolved:
    val obj_data = resolved_mod.object_data??
        return Err("Module has no object file: {resolved_mod.module_name}")

    val temp_obj = "/tmp/simple_lib_{resolved_mod.module_name}.o"
    write_bytes_to_file(temp_obj, obj_data)?
    all_objects.push(temp_obj)
```

### Phase 3b: Format Extension (1 day)

**Extended Library Format:**
```
LibSmfEntryExtended:
  - name (64 bytes)
  - smf_offset (8 bytes)
  - smf_size (8 bytes)
  - smf_hash (8 bytes)
  - obj_offset (8 bytes)      # NEW
  - obj_size (8 bytes)        # NEW
  - obj_hash (8 bytes)        # NEW
  - has_object (1 byte)       # NEW
  - reserved (23 bytes)
```

### Phase 3c: Testing (1 day)

**Test Cases:**
1. Link simple program against library
2. Verify symbol resolution
3. Test undefined symbols
4. Cross-platform compatibility

## Alternative: Workaround for v0.5.0

If full implementation is deferred, document workaround:

**Workaround: Source-Level Linking**
```bash
# Instead of linking against libraries, recompile from source
simple compile src/std/io/mod.spl -o std_io.o
simple compile src/my_app.spl -o my_app.o
ld std_io.o my_app.o -o my_app
```

**Pros:** Works now, no changes needed
**Cons:** Slower build, no library benefits

## Conclusion

**Immediate Action:** Implement Solution 3 (Hybrid Pre-Generation)
- **Effort:** 2-4 days
- **Benefit:** Complete Phase 3, enable native linking
- **Risk:** Low - builds on existing pipeline

**Future Work:** Transition to Solution 2 (MIR Reconstruction)
- **Timeline:** v0.6.0 or v1.0
- **Benefit:** Cleaner architecture, better optimization
- **Risk:** Medium - requires SMF format change

**Status:** Design approved, ready for implementation

---

**Author:** Simple Language Team
**Version:** 1.0
**Next Step:** Begin Phase 3a implementation
