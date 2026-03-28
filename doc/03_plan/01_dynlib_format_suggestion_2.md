# Dynamic Library Format Suggestion - Part 2

Part of [Dynamic Library Format Suggestion](01_dynlib_format_suggestion.md).

    uint32_t code_size;        // Size of native code

    uint16_t max_locals;       // For stack frame allocation
    uint16_t param_count;

    uint16_t attributes_count;
    attribute_info attributes[attributes_count];
};

// Effect types (Simple-specific)
enum Effect {
    EFFECT_NONE     = 0,
    EFFECT_WAITLESS = 1,
    EFFECT_ASYNC    = 2,
};
```

---

## Attributes (Inspired by Java)

Extensible attribute system allows future additions without format changes:

```c
struct attribute_info {
    uint16_t name_idx;         // Constant pool UTF8 for attribute name
    uint32_t length;           // Byte length of info
    uint8_t  info[length];     // Attribute-specific data
};
```

### Standard Attributes

| Attribute Name | Applies To | Purpose |
|----------------|------------|---------|
| `LineNumberTable` | Function | Source line mapping |
| `LocalVariableTable` | Function | Debug: local var names |
| `SourceFile` | Module | Original source filename |
| `Signature` | Type, Function | Generic type signature |
| `Deprecated` | Any | Mark as deprecated |
| `ConstantValue` | Field | Compile-time constant |
| `Exceptions` | Function | Thrown exception types |
| `ReloadInfo` | Function | Hot reload trampoline ID |
| `VerifyHints` | Function | Type verification data |

### ReloadInfo Attribute (Simple-specific)

```c
struct ReloadInfo_attribute {
    uint16_t name_idx;         // "ReloadInfo"
    uint32_t length;
    uint32_t trampoline_id;    // Index in global trampoline table
    uint32_t version;          // Function version for reload
    uint64_t layout_hash;      // Hash of signature (breaking change detection)
};
```

### LineNumberTable Attribute (from Java)

```c
struct LineNumberTable_attribute {
    uint16_t name_idx;         // "LineNumberTable"
    uint32_t length;
    uint16_t table_length;
    {
        uint16_t start_pc;     // Offset in code
        uint16_t line_number;  // Source line
    } entries[table_length];
};
```

---

## Relocation Table

Relocations use constant pool references for symbolic linking:

```c
struct Relocation {
    uint32_t offset;           // Position in code section
    uint16_t symbol_idx;       // Constant pool index (FunctionRef, FieldRef, etc.)
    uint8_t  type;             // Relocation type
    int32_t  addend;           // Constant addend
};

enum RelocationType {
    RELOC_ABS64       = 1,     // Absolute 64-bit
    RELOC_PC32        = 2,     // PC-relative 32-bit
    RELOC_PLT32       = 3,     // PLT/trampoline call
    RELOC_GOTPCREL    = 4,     // GOT-relative
    RELOC_TRAMPOLINE  = 5,     // Hot-reload trampoline (Simple-specific)
};
```

---

## Hot Reload Support

### Reload Safety Checks

1. **Layout Hash**: Each type has a `layout_hash`. If changed, instances must be migrated
2. **Symbol Versioning**: Functions have versions; callers check version matches
3. **State Migration**: Optional `migrate()` function per type for data transformation

### Reload Protocol

```
1. Load new .smf into memory (don't activate)
2. Compare type layout hashes
   - If unchanged: safe to swap
   - If changed: check for migrate() function
3. Pause actor message processing
4. Update trampoline table pointers atomically
5. Resume execution
6. GC will clean up old code when no references
```

### Trampoline Table

For hot-reloadable functions, use indirect calls:

```
call_table[func_id] -> current implementation pointer

# Reload updates:
atomic_store(&call_table[func_id], new_implementation)
```

---

## SMF Loading Modes

SMF supports two loading modes, allowing flexibility between quick startup and optimized runtime:

### Mode 1: Standalone Loading (As-Is)

Load SMF directly into its own memory region, like traditional .so/.dll:

```
┌─────────────────────────────────────────────────────────────┐
│  STANDALONE MODE                                            │
│                                                             │
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐         │
│  │   SMF A     │  │   SMF B     │  │   SMF C     │         │
│  │ ┌─────────┐ │  │ ┌─────────┐ │  │ ┌─────────┐ │         │
│  │ │  Code   │ │  │ │  Code   │ │  │ │  Code   │ │         │
│  │ ├─────────┤ │  │ ├─────────┤ │  │ ├─────────┤ │         │
│  │ │  Data   │ │  │ │  Data   │ │  │ │  Data   │ │         │
│  │ └─────────┘ │  │ └─────────┘ │  │ └─────────┘ │         │
│  └─────────────┘  └─────────────┘  └─────────────┘         │
│       ↑               ↑               ↑                     │
│    mmap'd          mmap'd          mmap'd                   │
└─────────────────────────────────────────────────────────────┘
```

**Characteristics:**
- Fast initial load (just mmap the file)
- Each module in separate memory region
- Direct calls within module, PLT-style for cross-module
- Good for: single module, quick scripts, development

### Mode 2: Settlement Loading (Optimized)

Move SMF into Settlement Space for better runtime performance:

```
┌─────────────────────────────────────────────────────────────┐
│  SETTLEMENT MODE                                            │
│                                                             │
│  ┌───────────────────────────────────────────────────────┐  │
│  │ CODE REGION: │ A code │ B code │ C code │   free    │  │  │
│  └───────────────────────────────────────────────────────┘  │
│  ┌───────────────────────────────────────────────────────┐  │
│  │ DATA REGION: │ A data │ B data │ C data │   free    │  │  │
│  └───────────────────────────────────────────────────────┘  │
│  ┌───────────────────────────────────────────────────────┐  │
│  │ INDIRECTION: │ func_table │ global_table │ type_table│  │  │
│  └───────────────────────────────────────────────────────┘  │
└─────────────────────────────────────────────────────────────┘
```

**Characteristics:**
- Merged by section type (better cache locality)
- All calls through indirection tables
- Easy hot reload, add/remove modules
- Good for: production, long-running apps, hot reload

### Mode Comparison

| Aspect | Standalone | Settlement |
|--------|------------|------------|
| Load time | Fast (mmap) | Slower (copy + relocate) |
| Memory layout | Scattered | Contiguous |
| Cache locality | Poor | Excellent |
| Hot reload | Replace whole file | Update table pointer |
| Module removal | OS unmap | Mark slots free |
| Cross-module calls | PLT overhead | Table lookup |
| Best for | Dev/scripts | Production/servers |

### Hybrid Approach

```c
// Load standalone first for quick start
SMF* module = smf_load_standalone("mymodule.smf");

// Later, migrate to settlement for performance
settlement_migrate(settlement, module);
smf_unload_standalone(module);  // Original can be unmapped
```

### Runtime Decision

```c
enum LoadMode {
    LOAD_STANDALONE,    // Quick load, own memory
    LOAD_SETTLEMENT,    // Copy into settlement
    LOAD_AUTO,          // Runtime decides based on:
                        //   - Module count (>3 → settlement)
                        //   - Hot reload flag (yes → settlement)
                        //   - Memory pressure (high → standalone)
};

ModuleHandle smf_load(const char* path, LoadMode mode);
```

---

## Settlement Space (Runtime Module Container)

The Settlement Space is a runtime memory region where multiple SMF modules are merged by section type. This design enables:
- **Easy Module Addition**: New modules slot into existing regions
- **Easy Module Removal**: Modules can be unloaded without fragmentation
- **Fast Address Updates**: All references go through indirection tables

### Settlement Space Layout

```
┌─────────────────────────────────────────────────────────────────────────┐
│                        SETTLEMENT SPACE                                  │
├─────────────────────────────────────────────────────────────────────────┤
│  ┌───────────────────────────────────────────────────────────────────┐  │
│  │ CODE REGION (RX - Read/Execute)                                   │  │
│  │ ┌─────────┬─────────┬─────────┬─────────┬─────────────────────┐   │  │
│  │ │ Module A│ Module B│ Module C│  FREE   │      FREE SPACE     │   │  │
│  │ │  Code   │  Code   │  Code   │  SLOT   │                     │   │  │
│  │ └─────────┴─────────┴─────────┴─────────┴─────────────────────┘   │  │
│  └───────────────────────────────────────────────────────────────────┘  │
├─────────────────────────────────────────────────────────────────────────┤
│  ┌───────────────────────────────────────────────────────────────────┐  │
│  │ DATA REGION (RW - Read/Write)                                     │  │
│  │ ┌─────────┬─────────┬─────────┬─────────┬─────────────────────┐   │  │
│  │ │ Module A│ Module B│ Module C│  FREE   │      FREE SPACE     │   │  │
│  │ │  Data   │  Data   │  Data   │  SLOT   │                     │   │  │
│  │ └─────────┴─────────┴─────────┴─────────┴─────────────────────┘   │  │
│  └───────────────────────────────────────────────────────────────────┘  │
├─────────────────────────────────────────────────────────────────────────┤
│  ┌───────────────────────────────────────────────────────────────────┐  │
│  │ INDIRECTION TABLES (RW)                                           │  │
│  │ ┌──────────────────┬──────────────────┬────────────────────────┐  │  │
│  │ │ Function Table   │ Global Table     │ Type Info Table        │  │  │
│  │ │ (call targets)   │ (data pointers)  │ (RTTI pointers)        │  │  │
│  │ └──────────────────┴──────────────────┴────────────────────────┘  │  │
│  └───────────────────────────────────────────────────────────────────┘  │
├─────────────────────────────────────────────────────────────────────────┤
│  ┌───────────────────────────────────────────────────────────────────┐  │
│  │ MODULE REGISTRY (Metadata)                                        │  │
│  │ ┌─────────┬─────────┬─────────┬─────────────────────────────────┐ │  │
│  │ │ Mod A   │ Mod B   │ Mod C   │           FREE                  │ │  │
│  │ │ Entry   │ Entry   │ Entry   │                                 │ │  │
│  │ └─────────┴─────────┴─────────┴─────────────────────────────────┘ │  │
│  └───────────────────────────────────────────────────────────────────┘  │
└─────────────────────────────────────────────────────────────────────────┘
```

### Indirection Tables

All cross-module references use indirection tables, enabling O(1) address updates:

```c
// Global Function Table - all calls go through here
struct FunctionTable {
    uint32_t capacity;
    uint32_t count;
    FunctionSlot slots[];
};

struct FunctionSlot {
    void*    code_ptr;           // Current implementation address
    uint32_t module_id;          // Owning module (for removal)
    uint32_t version;            // For hot reload detection
    uint16_t name_hash;          // Quick lookup
    uint16_t flags;              // OCCUPIED, FREE, TOMBSTONE
};

// Global Data Table - all global variable access goes through here
struct GlobalTable {
    uint32_t capacity;
    uint32_t count;
    GlobalSlot slots[];
};

struct GlobalSlot {
    void*    data_ptr;           // Current data address
    uint32_t module_id;          // Owning module
    uint32_t size;               // For bounds checking
    uint16_t flags;
};

// Type Info Table - for runtime type information
struct TypeTable {
    uint32_t capacity;
    uint32_t count;
    TypeSlot slots[];
};

struct TypeSlot {
    TypeInfo* info_ptr;          // Type metadata
    uint32_t  module_id;
    uint64_t  layout_hash;       // For compatibility checking
};
```

### Module Registry Entry

```c
struct ModuleEntry {
    uint32_t module_id;          // Unique ID in settlement
    uint32_t name_hash;          // Quick lookup by name
    uint16_t name_idx;           // Index to name string
    uint16_t flags;              // LOADED, UNLOADING, FAILED

    // Code region allocation
    uint32_t code_offset;        // Offset in CODE REGION
    uint32_t code_size;          // Size of code block

    // Data region allocation
    uint32_t data_offset;        // Offset in DATA REGION
    uint32_t data_size;          // Size of data block

    // Symbol ranges in indirection tables
    uint32_t func_start_idx;     // First function slot
    uint32_t func_count;         // Number of functions
    uint32_t global_start_idx;   // First global slot
    uint32_t global_count;       // Number of globals
    uint32_t type_start_idx;     // First type slot
    uint32_t type_count;         // Number of types

    // Dependencies
    uint16_t dep_count;
    uint32_t dependencies[];     // Module IDs this depends on
};
```

### Slot-Based Allocation

Uses slot allocator for efficient add/remove without fragmentation:

```c
// Slot allocator for each region
struct SlotAllocator {
    uint32_t slot_size;          // Fixed size per slot (e.g., 64KB)
    uint32_t total_slots;
    uint64_t free_bitmap[];      // 1 = free, 0 = occupied
};

// Allocation returns contiguous slots
struct Allocation {
    uint32_t start_slot;
    uint32_t slot_count;
};
```

**Slot sizes by region:**
| Region | Slot Size | Rationale |
|--------|-----------|-----------|
| Code | 64 KB | Typical module code size |
| Data | 16 KB | Smaller data footprint |
| Tables | 4 KB | Page-aligned entries |

### Adding a Module

```
1. Parse SMF header, validate compatibility
2. Allocate slots in CODE REGION (based on code_size)
3. Allocate slots in DATA REGION (based on data_size)
4. Reserve slots in indirection tables
5. Copy code to CODE REGION
6. Copy data to DATA REGION
7. Apply relocations:
   - Internal refs: direct offsets within module
   - External refs: update to use indirection table indices
8. Register functions/globals in indirection tables
9. Add ModuleEntry to registry
10. Update dependent modules' indirection entries if needed
```

```c
// Adding module - pseudocode
ModuleHandle settlement_add_module(Settlement* s, SMF* smf) {
    // Allocate space
    Allocation code_alloc = slot_alloc(&s->code_region, smf->code_size);
    Allocation data_alloc = slot_alloc(&s->data_region, smf->data_size);

    // Copy code and data
    memcpy(s->code_base + code_alloc.offset, smf->code, smf->code_size);
    memcpy(s->data_base + data_alloc.offset, smf->data, smf->data_size);

    // Reserve indirection slots
    uint32_t func_base = table_reserve(&s->func_table, smf->func_count);
    uint32_t glob_base = table_reserve(&s->global_table, smf->global_count);

    // Apply relocations using indirection
    apply_relocations(s, smf, code_alloc.offset, func_base, glob_base);

    // Register in tables
    for (int i = 0; i < smf->func_count; i++) {
        s->func_table[func_base + i] = (FunctionSlot){
            .code_ptr = s->code_base + code_alloc.offset + smf->funcs[i].offset,
            .module_id = new_module_id,
            .version = 1
        };
    }

    // Create registry entry
    return register_module(s, smf, code_alloc, data_alloc, func_base, glob_base);
}
```

### Removing a Module

```
1. Check no other modules depend on this module
2. Mark module as UNLOADING
3. Wait for any active calls to complete (if needed)
4. Mark indirection table slots as TOMBSTONE
5. Free CODE REGION slots
6. Free DATA REGION slots
7. Remove ModuleEntry from registry
8. Optionally compact (defragment) regions
```

```c
// Removing module - pseudocode
bool settlement_remove_module(Settlement* s, ModuleHandle h) {
    ModuleEntry* entry = get_entry(s, h);

    // Check dependencies
    if (has_dependents(s, h)) {
        return false;  // Cannot remove: others depend on it
    }

    // Mark as unloading
    entry->flags = MOD_UNLOADING;

    // Invalidate indirection entries
    for (uint32_t i = 0; i < entry->func_count; i++) {
        s->func_table[entry->func_start_idx + i].flags = SLOT_TOMBSTONE;
        s->func_table[entry->func_start_idx + i].code_ptr = &trap_handler;
    }

    // Free slots
    slot_free(&s->code_region, entry->code_offset, entry->code_size);
    slot_free(&s->data_region, entry->data_offset, entry->data_size);

    // Remove from registry
    unregister_module(s, h);

    return true;
}
```

### Call Indirection (Generated Code)

All inter-module calls use the function table:

```asm
; Direct call (intra-module, same SMF)
call    function_label

; Indirect call (inter-module, through settlement)
mov     rax, [func_table + FUNC_IDX * 8]   ; Load current address
call    rax                                  ; Call through pointer

; With hot-reload version check (optional)
mov     rax, [func_table + FUNC_IDX * 8]
cmp     dword [func_version + FUNC_IDX * 4], expected_version
jne     .version_mismatch
call    rax
```

### Benefits of Settlement Space

| Feature | Traditional DLL/SO | Settlement Space |
|---------|-------------------|------------------|
| Add module | Load into new memory | Slot into existing region |
| Remove module | dlclose (problematic) | Mark slots free |
| Update addresses | Patch all call sites | Update one table entry |
| Memory layout | Scattered | Contiguous by type |
| Cache locality | Poor (code scattered) | Good (code together) |
| Hot reload | Complex | Update table pointer |
| Defragmentation | Not possible | Compact and update tables |

### Compaction (Optional)

When fragmentation becomes significant:

```
1. Pause execution at safe point
2. For each occupied slot from end:
   - Find free slot earlier in region
   - Copy data to new location
   - Update indirection table entry
3. Shrink region bounds
4. Resume execution
```

Since all references go through indirection tables, compaction only requires updating table entries, not patching code.

---

## Platform Abstraction

### Loading Strategy

| Platform | Native Format | SMF Strategy |
|----------|---------------|--------------|
| Linux | ELF .so | mmap() + manual relocation |
| Windows | PE .dll | VirtualAlloc() + manual relocation |
| macOS | Mach-O .dylib | mmap() + manual relocation |

### Why SMF Instead of Native Formats?

| Issue | Native (.so/.dll) | SMF |
|-------|-------------------|-----|
| Hot reload | Difficult (dlclose issues) | Built-in support |
| Symbol versioning | Limited | Per-symbol versions |
| Type metadata | None | Full type info |
| Cross-platform | Format differs | Single format |
| Load speed | OS loader overhead | Direct mmap |
| Extensibility | Fixed format | Attribute system |

---

## Performance Optimizations

1. **Memory-Mapped Loading**: mmap file, parse header, load on-demand
2. **Lazy Symbol Resolution**: PLT-style stubs, resolve on first call
3. **Pre-computed Hashes**: Symbol names have pre-computed hashes for O(1) lookup
4. **Section Alignment**: Page-aligned for efficient mmap
5. **Constant Pool Deduplication**: Same strings stored once

---

## File Extension Convention

| Extension | Description |
|-----------|-------------|
| `.smf` | Simple Module File (library) |
| `.sme` | Simple Module Executable (has entry point) |
| `.smi` | Simple Module Interface (headers only, for IDE) |
| `.smc` | Simple Module Cache (incremental compilation cache) |

---

## Comparison with Alternatives

| Format | Hot Reload | Type Info | Cross-Platform | Load Speed | Extensible |
|--------|------------|-----------|----------------|------------|------------|
| ELF .so | Hard | No | Linux only | Medium | No |
| PE .dll | Hard | No | Windows only | Medium | No |
| Java .class | Complex | Yes | Yes | Medium | Yes |
| WebAssembly | Yes | Yes | Yes | Slow | Yes |
| **SMF** | Yes | Yes | Yes | Fast | Yes |

---

## Implementation Priority

1. **Phase 1**: Header + Constant Pool + Code Section
2. **Phase 2**: Type Definitions + Function Table
3. **Phase 3**: Relocations with symbolic references
4. **Phase 4**: Settlement Space (indirection tables, module registry)
5. **Phase 5**: Attributes (debug info, source maps)
6. **Phase 6**: Hot reload support (leverages settlement indirection)
7. **Phase 7**: Verification hints
8. **Phase 8**: Settlement compaction

---

## Summary

The SMF format combines:

- **Java's constant pool** - Centralized, indexed, deduplicated references
- **Java's type descriptors** - Compact type encoding
- **Java's attributes** - Extensible metadata system
- **Native code** - AOT compiled, no JIT warmup
- **Hot reload** - Built-in trampoline support
- **Cross-platform** - Single format for all platforms
- **Dual-Mode Loading** - Standalone (fast) or Settlement (optimized)
- **Settlement Space** - Runtime container merging modules by section type

### Loading Mode Selection

```
┌─────────────────────────────────────────────────────────────┐
│  STANDALONE (as-is)          │  SETTLEMENT (optimized)      │
│  ─────────────────────────── │  ──────────────────────────  │
│  • mmap file directly        │  • Copy into merged regions  │
│  • Fast startup              │  • Better cache locality     │
│  • Good for dev/scripts      │  • Easy hot reload           │
│  • Each module separate      │  • Good for production       │
└─────────────────────────────────────────────────────────────┘
```

### Settlement Space Key Benefits

```
┌──────────────────────────────────────────────────────────┐
│  Traditional: Each module in separate memory regions     │
│  ┌────┐ ┌────┐ ┌────┐    Scattered, hard to manage      │
│  │ A  │ │ B  │ │ C  │                                    │
│  └────┘ └────┘ └────┘                                    │
├──────────────────────────────────────────────────────────┤
│  Settlement: All code together, all data together        │
│  ┌─────────────────────┐  Easy add/remove/update         │
│  │ A code │ B │ C │free│  via indirection tables         │
│  └─────────────────────┘                                 │
└──────────────────────────────────────────────────────────┘
```

This enables Simple programs to feel like scripted languages (quick iteration) while having ahead-of-time compiled performance.

---

## References

- [Java Virtual Machine Specification - Chapter 4: The class File Format](https://docs.oracle.com/javase/specs/jvms/se7/html/jvms-4.html)
- [Java class file - Wikipedia](https://en.wikipedia.org/wiki/Java_class_file)
---

Back to: [Part 1](01_dynlib_format_suggestion.md)
