# Dynamic Library Format Suggestion for Simple Language

## Overview

This document suggests a custom dynamic library format optimized for:
- **Performance**: Fast loading and symbol resolution
- **Flexibility**: Hot-reloadable modules
- **Cross-platform**: Works on Linux (.so) and Windows (.dll)
- **Interpreter-like**: Ahead-of-time compile, then run like script

---

## Design Inspiration: Java Class File Format

The SMF format incorporates key design patterns from [Java's class file format](https://docs.oracle.com/javase/specs/jvms/se7/html/jvms-4.html):

| Feature | Java .class | SMF Adoption |
|---------|-------------|--------------|
| Constant Pool | Centralized, indexed, deduplicated | ✅ Adopted |
| Type Descriptors | Compact encoding (`I`, `Ljava/lang/Object;`) | ✅ Adopted |
| Attributes | Extensible named attributes | ✅ Adopted |
| Symbolic References | All refs through constant pool | ✅ Adopted |
| Bytecode | Platform-independent bytecode | ❌ Native code instead |

**SMF Unique Features** (not in Java):
- Native machine code (AOT compiled)
- Hot reload with trampolines
- Platform-specific binaries

---

## Suggested Format: Simple Module Format (SMF)

### Design Goals

| Goal | Description |
|------|-------------|
| Fast Load | Memory-mapped, minimal parsing at load time |
| Hot Reload | Version tracking, safe symbol replacement |
| Incremental | Only recompile changed functions |
| Debug-friendly | Source maps, symbol names preserved |
| Platform Agnostic | Abstract over .so/.dll differences |
| Extensible | Attribute system for future additions |
| Dual-Mode Loading | Standalone (as-is) or Settlement (optimized) |
| Settlement Space | Merge modules by section, easy add/remove |

---

## File Structure: `.smf` (Simple Module File)

```
┌─────────────────────────────────────────┐
│ SMF Header (80+ bytes)                  │
├─────────────────────────────────────────┤
│ Constant Pool                           │  ← Strings, types, refs (from Java)
├─────────────────────────────────────────┤
│ Import Table                            │  ← External dependencies + hashes
├─────────────────────────────────────────┤
│ Export Table                            │  ← Public symbols + hashes
├─────────────────────────────────────────┤
│ Type Definitions                        │  ← Structs, Classes, Enums, Traits
├─────────────────────────────────────────┤
│ Function Table                          │  ← Method signatures + code refs
├─────────────────────────────────────────┤
│ Code Section (.text)                    │  ← Native machine code
├─────────────────────────────────────────┤
│ Data Section (.data)                    │  ← Initialized globals
├─────────────────────────────────────────┤
│ Relocation Table                        │  ← Symbolic relocations
├─────────────────────────────────────────┤
│ Attributes                              │  ← Debug info, source maps, etc.
└─────────────────────────────────────────┘
```

---

## Header Format (88 bytes)

```c
struct SMFHeader {
    uint8_t  magic[4];            // "SMF\0"
    uint8_t  version_minor;       // Format minor version
    uint8_t  version_major;       // Format major version
    uint8_t  platform;            // 0=portable, 1=linux-x64, 2=win-x64, 3=linux-arm64
    uint8_t  flags;               // Flags (see below)

    uint16_t constant_pool_count; // Constant pool entries (1-based like Java)
    uint16_t type_count;          // Number of type definitions
    uint16_t function_count;      // Number of functions
    uint16_t attribute_count;     // Module-level attributes

    uint32_t constant_pool_offset;
    uint32_t type_table_offset;
    uint32_t function_table_offset;
    uint32_t code_offset;
    uint32_t data_offset;
    uint32_t reloc_offset;
    uint32_t import_table_offset; // External dependencies (NEW)
    uint32_t export_table_offset; // Public symbols (NEW)
    uint32_t attribute_offset;

    uint32_t code_size;
    uint32_t data_size;

    uint32_t entry_function;      // Index of main() or 0
    uint32_t module_name_idx;     // Constant pool index for module name

    uint64_t source_hash;         // For rebuild detection
    uint64_t content_hash;        // For integrity/caching
    uint64_t api_hash;            // Hash of all exports (NEW) - quick compat check
};

// Flags
#define SMF_FLAG_EXECUTABLE    0x01  // Has entry point
#define SMF_FLAG_RELOADABLE    0x02  // Supports hot reload
#define SMF_FLAG_DEBUG_INFO    0x04  // Contains source maps
#define SMF_FLAG_VERIFIED      0x08  // Has verification hints
```

---

## Constant Pool (Inspired by Java)

The constant pool is a centralized, indexed repository for all strings, type references, and symbolic references. This enables:
- **Deduplication**: Same string stored once
- **Symbolic References**: Instructions reference pool indices
- **Smaller Files**: Share common strings/types

```c
// Constant pool entry header
struct cp_info {
    uint8_t tag;
    // Variable-length data follows based on tag
};

// Tags
enum ConstantTag {
    CONST_UTF8           = 1,   // UTF-8 string
    CONST_INT            = 3,   // i64 integer literal
    CONST_FLOAT          = 4,   // f64 float literal
    CONST_TYPE           = 7,   // Type descriptor reference
    CONST_STRING         = 8,   // String literal (ref to UTF8)
    CONST_FUNCTION_REF   = 10,  // Function reference
    CONST_FIELD_REF      = 11,  // Field reference
    CONST_NAME_AND_TYPE  = 12,  // Name + type descriptor pair
    CONST_MODULE_REF     = 13,  // External module reference
    CONST_TRAIT_REF      = 14,  // Trait reference
    CONST_SYMBOL         = 15,  // :symbol literal
    CONST_GLOBAL_REF     = 16,  // External global/variable reference
    CONST_MACRO_REF      = 17,  // Macro/inline constant reference
};
```

### Constant Pool Structures

```c
// UTF-8 String (interned)
struct CONST_Utf8_info {
    uint8_t  tag;            // 1
    uint16_t length;
    uint8_t  bytes[length];  // UTF-8 encoded
};

// Integer constant
struct CONST_Int_info {
    uint8_t tag;             // 3
    int64_t value;
};

// Float constant
struct CONST_Float_info {
    uint8_t tag;             // 4
    double  value;
};

// Type descriptor
struct CONST_Type_info {
    uint8_t  tag;            // 7
    uint16_t descriptor_idx; // Index to UTF8 with type descriptor
};

// Function reference (for calls)
struct CONST_FunctionRef_info {
    uint8_t  tag;               // 10
    uint16_t module_idx;        // 0 = current module, else ModuleRef index
    uint16_t name_and_type_idx; // Index to NameAndType
};

// Field reference
struct CONST_FieldRef_info {
    uint8_t  tag;               // 11
    uint16_t type_idx;          // Type containing the field
    uint16_t name_and_type_idx; // Index to NameAndType
};

// Name and Type (reused for methods and fields)
struct CONST_NameAndType_info {
    uint8_t  tag;               // 12
    uint16_t name_idx;          // UTF8 index for name
    uint16_t descriptor_idx;    // UTF8 index for type descriptor
};

// External module reference
struct CONST_ModuleRef_info {
    uint8_t  tag;               // 13
    uint16_t name_idx;          // UTF8 index for module name
    uint16_t version_idx;       // UTF8 index for version (or 0)
};

// External global/variable reference (NEW)
struct CONST_GlobalRef_info {
    uint8_t  tag;               // 16
    uint16_t module_idx;        // ModuleRef index
    uint16_t name_and_type_idx; // Index to NameAndType
};

// Macro/Inline constant reference (NEW)
struct CONST_MacroRef_info {
    uint8_t  tag;               // 17
    uint16_t module_idx;        // ModuleRef index
    uint16_t name_idx;          // UTF8 index for macro name
    uint64_t value_hash;        // Hash of expanded value (detect changes)
};
```

---

## External References & ABI Compatibility

SMF tracks all external dependencies with signature hashes to detect breaking changes at load time.

### Import Table

Each SMF has an import table listing all external symbols it depends on:

```c
struct ImportTable {
    uint16_t module_count;       // Number of imported modules
    uint16_t function_count;     // Number of imported functions
    uint16_t type_count;         // Number of imported types
    uint16_t global_count;       // Number of imported globals
    uint16_t macro_count;        // Number of imported macros/constants

    ImportedModule modules[module_count];
    ImportedFunction functions[function_count];
    ImportedType types[type_count];
    ImportedGlobal globals[global_count];
    ImportedMacro macros[macro_count];
};
```

### Imported Symbol Structures

```c
// Imported module dependency
struct ImportedModule {
    uint16_t name_idx;           // Module name (UTF8)
    uint16_t min_version_idx;    // Minimum compatible version
    uint16_t max_version_idx;    // Maximum compatible version (0 = any)
    uint64_t api_hash;           // Hash of used API surface
    uint16_t flags;              // REQUIRED, OPTIONAL, WEAK
};

// Imported function with signature hash
struct ImportedFunction {
    uint16_t module_idx;         // Which imported module
    uint16_t name_idx;           // Function name
    uint16_t descriptor_idx;     // Expected signature: (I,I)->I
    uint64_t signature_hash;     // Hash of full signature for fast check
    uint16_t flags;              // REQUIRED, OPTIONAL, WEAK_LINK
};

// Imported type with layout hash
struct ImportedType {
    uint16_t module_idx;         // Which imported module
    uint16_t name_idx;           // Type name
    uint64_t layout_hash;        // Hash of type layout (size, field offsets)
    uint64_t api_hash;           // Hash of public methods/fields
    uint16_t flags;              // REQUIRED, OPAQUE_OK (don't care about layout)
};

// Imported global variable
struct ImportedGlobal {
    uint16_t module_idx;         // Which imported module
    uint16_t name_idx;           // Variable name
    uint16_t descriptor_idx;     // Expected type
    uint64_t type_hash;          // Hash of type for compatibility
    uint16_t flags;              // REQUIRED, MUTABLE, IMMUTABLE
};

// Imported macro/inline constant
struct ImportedMacro {
    uint16_t module_idx;         // Which imported module
    uint16_t name_idx;           // Macro name
    uint64_t value_hash;         // Hash of value at compile time
    uint16_t flags;              // CONST_VALUE, INLINE_FUNC
};

// Import flags
#define IMPORT_REQUIRED    0x0001  // Must be present
#define IMPORT_OPTIONAL    0x0002  // Ok if missing (returns nil/default)
#define IMPORT_WEAK        0x0004  // Resolve at runtime, may fail
#define IMPORT_OPAQUE_OK   0x0008  // Type: don't care about internal layout
```

### Export Table

Each SMF declares what it exports with versioned signatures:

```c
struct ExportTable {
    uint16_t function_count;
    uint16_t type_count;
    uint16_t global_count;
    uint16_t macro_count;

    ExportedFunction functions[function_count];
    ExportedType types[type_count];
    ExportedGlobal globals[global_count];
    ExportedMacro macros[macro_count];
};

// Exported function
struct ExportedFunction {
    uint16_t name_idx;           // Public name
    uint16_t descriptor_idx;     // Signature
    uint32_t func_table_idx;     // Index in function table
    uint64_t signature_hash;     // For compatibility checking
    uint32_t since_version;      // When added (for deprecation)
    uint16_t flags;              // PUBLIC, DEPRECATED, INLINE
};

// Exported type
struct ExportedType {
    uint16_t name_idx;           // Public name
    uint32_t type_table_idx;     // Index in type table
    uint64_t layout_hash;        // Size + field offsets
    uint64_t api_hash;           // Public methods + fields
    uint32_t since_version;
    uint16_t flags;              // PUBLIC, OPAQUE, SEALED
};

// Exported global
struct ExportedGlobal {
    uint16_t name_idx;
    uint16_t descriptor_idx;
    uint32_t data_offset;        // Offset in data section
    uint64_t type_hash;
    uint16_t flags;              // PUBLIC, READONLY, MUTABLE
};

// Exported macro/constant
struct ExportedMacro {
    uint16_t name_idx;
    uint64_t value_hash;         // Detect if value changed
    uint16_t value_type;         // INT, FLOAT, STRING, INLINE_FUNC
    // Inline value follows based on type
};
```

### Breaking Change Detection

When loading SMF, check all imports against exports:

```c
enum CompatResult {
    COMPAT_OK,                   // All hashes match
    COMPAT_MINOR_CHANGE,         // Safe: new exports added
    COMPAT_FUNC_SIGNATURE,       // BREAKING: function signature changed
    COMPAT_TYPE_LAYOUT,          // BREAKING: type size/layout changed
    COMPAT_TYPE_API,             // BREAKING: type methods changed
    COMPAT_GLOBAL_TYPE,          // BREAKING: global variable type changed
    COMPAT_MACRO_VALUE,          // BREAKING: macro value changed
    COMPAT_MISSING_EXPORT,       // BREAKING: required export removed
};

CompatResult check_compatibility(SMF* importer, SMF* exporter) {
    for (ImportedFunction* imp : importer->imports.functions) {
        ExportedFunction* exp = find_export(exporter, imp->name_idx);

        if (!exp) {
            if (imp->flags & IMPORT_REQUIRED)
                return COMPAT_MISSING_EXPORT;
            continue;
        }

        // Fast path: hash match = compatible
        if (imp->signature_hash != exp->signature_hash) {
            return COMPAT_FUNC_SIGNATURE;
        }
    }

    for (ImportedType* imp : importer->imports.types) {
        ExportedType* exp = find_export(exporter, imp->name_idx);

        if (!exp) return COMPAT_MISSING_EXPORT;

        // Layout hash: size, alignment, field offsets
        if (!(imp->flags & IMPORT_OPAQUE_OK)) {
            if (imp->layout_hash != exp->layout_hash)
                return COMPAT_TYPE_LAYOUT;
        }

        // API hash: method signatures
        if (imp->api_hash != exp->api_hash)
            return COMPAT_TYPE_API;
    }

    // Similar checks for globals and macros...
    return COMPAT_OK;
}
```

### Hash Computation

```c
// Function signature hash
uint64_t compute_signature_hash(Function* f) {
    Hash h;
    hash_add(&h, f->name);
    hash_add(&h, f->return_type_descriptor);
    for (Param* p : f->params) {
        hash_add(&h, p->type_descriptor);
    }
    hash_add(&h, f->effect);  // async, async
    return hash_finalize(&h);
}

// Type layout hash (breaking if changed)
uint64_t compute_layout_hash(Type* t) {
    Hash h;
    hash_add(&h, t->size);
    hash_add(&h, t->alignment);
    for (Field* f : t->fields) {
        hash_add(&h, f->offset);
        hash_add(&h, f->type_descriptor);
    }
    return hash_finalize(&h);
}

// Type API hash (methods + public fields)
uint64_t compute_api_hash(Type* t) {
    Hash h;
    for (Field* f : t->public_fields) {
        hash_add(&h, f->name);
        hash_add(&h, f->type_descriptor);
    }
    for (Method* m : t->public_methods) {
        hash_add(&h, compute_signature_hash(m));
    }
    return hash_finalize(&h);
}

// Macro value hash
uint64_t compute_macro_hash(Macro* m) {
    Hash h;
    hash_add(&h, m->name);
    hash_add(&h, m->expanded_value);  // Literal bytes
    return hash_finalize(&h);
}
```

### What Changes Are Breaking?

| Change | Import Check | Result |
|--------|--------------|--------|
| Add new export | - | OK (minor) |
| Remove export | Missing required | BREAKING |
| Change function params | signature_hash | BREAKING |
| Change return type | signature_hash | BREAKING |
| Add function param with default | signature_hash | BREAKING* |
| Change type size | layout_hash | BREAKING |
| Add field to struct | layout_hash | BREAKING |
| Reorder fields | layout_hash | BREAKING |
| Add method to type | api_hash | BREAKING |
| Change method signature | api_hash | BREAKING |
| Change global type | type_hash | BREAKING |
| Change macro value | value_hash | BREAKING |
| Change macro to different value type | value_hash | BREAKING |

*Simple doesn't have default params, so all param changes break

### Load-Time Verification

```
1. Load SMF header
2. Parse import table
3. For each imported module:
   a. Find loaded module or load it
   b. check_compatibility(this, imported_module)
   c. If BREAKING: reject load with detailed error
4. If all compatible: proceed with relocation
5. Bind imports to actual addresses
```

### Detailed Error Messages

```
Error: Cannot load module 'game.smf'

  Import 'math.Vector3' has incompatible layout:
    Expected: layout_hash=0x1a2b3c4d (size=24, align=8)
    Found:    layout_hash=0x5e6f7a8b (size=32, align=8)

  The type 'Vector3' in 'math.smf' has changed since 'game.smf' was compiled.

  Breaking changes detected:
    - Field added: 'w' at offset 24 (f64)

  Solution: Recompile 'game.smf' against new 'math.smf'
```

---

## Compact Type Descriptors (Inspired by Java)

Instead of storing full type structures, use compact string descriptors:

### Base Types
```
I  = i64
F  = f64
B  = bool
C  = char
S  = str
N  = Nil
Y  = Symbol
```

### Compound Types
```
Lmodule/TypeName;     = Named type (struct, class, enum)
Tmodule/TraitName;    = Trait reference
Amodule/ActorName;    = Actor reference

[T                    = Array of T
(T,T,T)               = Tuple of types
{K:V}                 = Dict with key K, value V
?T                    = Optional T (T | Nil)
T|U                   = Union type

(T,T)->R              = Function type: (params) -> return
```

### Pointer Types (Simple-specific)
```
&T    = Unique pointer
*T    = Shared pointer (refcounted)
-T    = Weak pointer
+T    = Handle pointer
~T    = Borrowed reference
```

### Examples
```
I                                → i64
[I                               → [i64]
[[F                              → [[f64]]
Lmath/Vector3;                   → math.Vector3
[Lgame/Entity;                   → [game.Entity]
(I,I)->I                         → fn(i64, i64) -> i64
(Lnet/Request;)->Lnet/Response;  → fn(Request) -> Response
?Lcore/Error;                    → Error?
&Lgame/Player;                   → &Player (unique pointer)
*Lgame/Enemy;                    → *Enemy (shared pointer)
+Lgame/Bullet;                   → +Bullet (handle pointer)
```

**Size Comparison:**
- Full type struct: 48+ bytes
- Type descriptor: `Lmath/Vector3;` = 15 bytes (shared in pool)

---

## Type Definitions

```c
struct TypeDef {
    uint16_t access_flags;     // PUBLIC, FINAL, ABSTRACT, etc.
    uint16_t name_idx;         // Constant pool UTF8 index
    uint16_t descriptor_idx;   // Type descriptor index
    uint8_t  kind;             // STRUCT, CLASS, ENUM, TRAIT, ACTOR
    uint8_t  flags;            // MUTABLE, IMMUTABLE, etc.

    uint16_t super_type_idx;   // Parent type (0 if none)
    uint16_t interfaces_count;
    uint16_t interfaces[interfaces_count];  // Trait indices

    uint16_t fields_count;
    field_info fields[fields_count];

    uint16_t methods_count;
    uint16_t methods[methods_count];  // Indices into function table

    uint16_t attributes_count;
    attribute_info attributes[attributes_count];
};

struct field_info {
    uint16_t access_flags;
    uint16_t name_idx;
    uint16_t descriptor_idx;
    uint16_t attributes_count;
    attribute_info attributes[attributes_count];
};

// Type kinds
enum TypeKind {
    KIND_STRUCT  = 1,
    KIND_CLASS   = 2,
    KIND_ENUM    = 3,
    KIND_TRAIT   = 4,
    KIND_ACTOR   = 5,
};

// Access flags (like Java)
#define ACC_PUBLIC      0x0001
#define ACC_PRIVATE     0x0002
#define ACC_PROTECTED   0x0004
#define ACC_STATIC      0x0008
#define ACC_FINAL       0x0010
#define ACC_MUTABLE     0x0020   // Simple-specific
#define ACC_IMMUTABLE   0x0040   // Simple-specific
#define ACC_ABSTRACT    0x0400
#define ACC_SYNTHETIC   0x1000
```

---

## Function Table

```c
struct FunctionDef {
    uint16_t access_flags;
    uint16_t name_idx;         // Constant pool UTF8
    uint16_t descriptor_idx;   // Type descriptor for signature
    uint8_t  effect;           // NONE, WAITLESS, ASYNC
    uint8_t  flags;            // RELOADABLE, INLINE, etc.

    uint32_t code_offset;      // Offset into code section
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
