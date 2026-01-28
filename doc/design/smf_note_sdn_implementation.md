# SMF note.sdn Implementation Summary

## Overview

Implemented the `note.sdn` section for SMF files to track generic instantiation metadata. This enables lazy/on-demand instantiation at link-time and load-time, along with circular dependency detection.

## Implementation Status

### ✅ Phase 1: Basic note.sdn Writing (COMPLETE)

**Rust Implementation:**
- Created `src/rust/compiler/src/monomorphize/note_sdn.rs` with full data structures
- Updated `src/rust/compiler/src/smf_writer.rs` to write note.sdn sections
- Section uses zero-size trick: `size=0` in section table, actual size determined by `\n# END_NOTE\n` terminator

**Simple Implementation:**
- Created `simple/compiler/monomorphize/note_sdn.spl` with equivalent data structures
- Updated `simple/compiler/smf_writer.spl` to serialize note.sdn sections
- Created comprehensive test suite in `test/lib/std/unit/compiler/note_sdn_spec.spl`

## Architecture

### SMF File Structure (with note.sdn)

```
┌─────────────────────────────────┐
│ Section: Code                   │
│ Section: Data                   │
│ Section: RoData                 │
│ Section: TemplateCode           │ ← Generic templates
│ Section: TemplateMeta           │ ← Monomorphization metadata
│ Section: note.sdn               │ ← ⭐ NEW: Instantiation tracking (size=0)
├─────────────────────────────────┤
│ Section Table                   │
├─────────────────────────────────┤
│ Header (128 bytes at EOF-128)   │ ← Trailer design
└─────────────────────────────────┘
```

### Zero-Size Mechanism

**Section Table Entry:**
```rust
SmfSection {
    section_type: SectionType::TemplateMeta,  // Reuse existing type
    flags: SECTION_FLAG_READ,
    offset: 0x12345,    // Where data starts
    size: 0,            // ⭐ Always 0
    virtual_size: 0,
    alignment: 1,
    name: b"note.sdn\0\0\0\0\0\0\0\0",  // 16 bytes
}
```

**Why size=0?**
- Hot-reload can update data without modifying section table
- Data can grow/shrink until next section boundary
- Similar to ZIP central directory design

## SDN Schema

### Tables in note.sdn

1. **`instantiations`** - What was compiled
   - Columns: `id, template, type_args, mangled_name, from_file, from_loc, to_obj, status`
   - Example: `0, "List", "Int", "List$Int", "app.spl", "app.spl:10:5", "app.o", "compiled"`

2. **`possible`** - Can be lazily generated
   - Columns: `id, template, type_args, mangled_name, required_by, can_defer`
   - Example: `0, "Option", "Float", "Option$Float", "math_module", true`

3. **`type_inferences`** - Type inference events
   - Columns: `id, inferred_type, expr, context, from_file, from_loc`
   - Example: `0, "Int", "42", "literal", "app.spl", "app.spl:5:10"`

4. **`dependencies`** - Instantiation graph edges
   - Columns: `from_inst, to_inst, dep_kind`
   - Example: `"List$Int", "Int", "type_param"`

5. **`circular_warnings`** - Soft cycles (warnings)
   - Columns: `id, cycle_path, severity`
   - Example: `0, "Node$T->Option$Node$T->Node$T", "warning"`

6. **`circular_errors`** - Hard cycles (errors)
   - Columns: `id, cycle_path, error_code`
   - Example: `0, "A$T->B$T->C$T->A$T", "E0420"`

### Example note.sdn Content

```sdn
# Instantiation To/From Metadata
# Format version: 1.0

instantiations |id, template, type_args, mangled_name, from_file, from_loc, to_obj, status|
    0, "List", "Int", "List$Int", "app.spl", "app.spl:10:5", "app.o", "compiled"
    1, "Option", "String", "Option$String", "lib.spl", "lib.spl:42:3", "lib.o", "compiled"

possible |id, template, type_args, mangled_name, required_by, can_defer|
    0, "List", "Float", "List$Float", "math_module", true

type_inferences |id, inferred_type, expr, context, from_file, from_loc|
    0, "Int", "42", "literal", "app.spl", "app.spl:5:10"

dependencies |from_inst, to_inst, dep_kind|
    "List$Int", "Int", "type_param"
    "Option$String", "String", "type_param"

circular_warnings |id, cycle_path, severity|
    0, "Node$T->Option$Node$T->Node$T", "warning"

circular_errors |id, cycle_path, error_code|

# END_NOTE
```

## Data Structures

### Rust API

```rust
// Core metadata structure
pub struct NoteSdnMetadata {
    pub instantiations: Vec<InstantiationEntry>,
    pub possible: Vec<PossibleInstantiationEntry>,
    pub type_inferences: Vec<TypeInferenceEntry>,
    pub dependencies: Vec<DependencyEdge>,
    pub circular_warnings: Vec<CircularWarning>,
    pub circular_errors: Vec<CircularError>,
}

// Instantiation entry
pub struct InstantiationEntry {
    pub template: String,
    pub type_args: String,
    pub mangled_name: String,
    pub from_file: String,
    pub from_loc: String,
    pub to_obj: String,
    pub status: InstantiationStatus,
}

pub enum InstantiationStatus {
    Compiled,      // Compiled to native code
    Deferred,      // Deferred for lazy compilation
    JitCompiled,   // JIT-compiled at runtime
}

// Dependency tracking
pub struct DependencyEdge {
    pub from_inst: String,
    pub to_inst: String,
    pub dep_kind: DependencyKind,
}

pub enum DependencyKind {
    TypeParam,    // Type parameter dependency
    FieldType,    // Field type dependency
    InnerType,    // Inner type dependency
    MethodDep,    // Method dependency
}
```

### Simple API

```simple
# Core metadata structure
struct NoteSdnMetadata:
    instantiations: [InstantiationEntry]
    possible: [PossibleInstantiationEntry]
    type_inferences: [TypeInferenceEntry]
    dependencies: [DependencyEdge]
    circular_warnings: [CircularWarning]
    circular_errors: [CircularError]

# Methods
impl NoteSdnMetadata:
    static fn new() -> NoteSdnMetadata
    fn is_empty() -> bool
    me add_instantiation(entry: InstantiationEntry)
    fn to_sdn() -> text
```

## Usage Examples

### Writing note.sdn (Rust)

```rust
use simple_compiler::monomorphize::{NoteSdnMetadata, InstantiationEntry, InstantiationStatus};
use simple_compiler::smf_writer::generate_smf_with_all_sections;

// Create metadata
let mut note = NoteSdnMetadata::new();

// Track instantiation
note.add_instantiation(InstantiationEntry::new(
    "List".to_string(),
    vec![ConcreteType::Named("Int".to_string())],
    "List$Int".to_string(),
    "app.spl".to_string(),
    "app.spl:10:5".to_string(),
    "app.o".to_string(),
    InstantiationStatus::Compiled,
));

// Generate SMF with note.sdn
let smf_bytes = generate_smf_with_all_sections(
    &object_code,
    Some(&templates),
    Some(&metadata),
    Some(&note),
    None,
    target,
);
```

### Writing note.sdn (Simple)

```simple
use simple/compiler/monomorphize/note_sdn.*

# Create metadata
var note = NoteSdnMetadata.new()

# Track instantiation
note.add_instantiation(InstantiationEntry.new(
    template: "List",
    type_args: [ConcreteType.Named("Int", [])],
    mangled_name: "List$Int",
    from_file: "app.spl",
    from_loc: "app.spl:10:5",
    to_obj: "app.o",
    status: InstantiationStatus.Compiled
))

# Serialize to SDN
val sdn_text = note.to_sdn()
```

## Testing

### Unit Tests

**Rust:**
- `src/rust/compiler/src/monomorphize/note_sdn.rs` contains inline tests
- Tests: empty metadata, entry creation, SDN serialization, escaping

**Simple:**
- `test/lib/std/unit/compiler/note_sdn_spec.spl` contains SSpec tests
- 13 test cases covering all functionality
- Tests: metadata creation, entry addition, SDN format, escaping

### Running Tests

```bash
# Rust tests
cargo test -p simple-compiler note_sdn

# Simple tests
./target/debug/simple_old test test/lib/std/unit/compiler/note_sdn_spec.spl
```

## Next Phases

### 🔜 Phase 2: note.sdn Reading (Loader)

**Goals:**
- Load note.sdn section from SMF files
- Parse SDN format
- Build dependency graph

**Files to create:**
- `src/rust/loader/src/smf/note_loader.rs`
- `simple/compiler/loader/note_loader.spl`

**Tasks:**
1. Find section by name="note.sdn"
2. Scan from offset until `# END_NOTE\n`
3. Parse SDN format
4. Build dependency graph

### 🔜 Phase 3: Compile-Time Tracking

**Goals:**
- Track instantiations during monomorphization
- Track type inference events
- Analyze for possible future instantiations
- Build dependency graph

**Files to modify:**
- `src/rust/compiler/src/monomorphize/engine.rs`
- `src/rust/compiler/src/hir/lower/expr/inference.rs`

### 🔜 Phase 4: Link-Time Lazy Instantiation

**Goals:**
- Load note.sdn from all input SMFs
- Check for missing symbols
- Generate missing instantiations from `possible` table

**Files to create:**
- `src/rust/compiler/src/linker/lazy_instantiator.rs`

### 🔜 Phase 5: Load-Time JIT Instantiation

**Goals:**
- On symbol lookup failure, check note.sdn
- Load template from TemplateCode section
- JIT-compile or interpret

**Files to create:**
- `src/rust/loader/src/smf/jit_instantiator.rs`

### 🔜 Phase 6: Circular Dependency Detection

**Goals:**
- Build dependency graph from note.sdn
- DFS cycle detection
- Classify: hard error (E0420) vs soft warning

**Files to create:**
- `src/rust/compiler/src/monomorphize/cycle_detector.rs`

### 🔜 Phase 7: Hot-Reload Support

**Goals:**
- Implement dynamic note.sdn update
- Check data growth against next section
- Handle overflow (trigger rebuild)

### 🔜 Phase 8: Simple Compiler Port

**Goals:**
- Port all functionality to Simple language
- Add comprehensive SSpec tests

## Key Design Decisions

### 1. Zero-Size Section Table Entry

**Rationale:** Allows hot-reload updates without modifying section table. Data can grow/shrink dynamically until next section boundary.

**Trade-off:** Requires scanning for terminator to determine actual size. This is acceptable because note.sdn is only read at link/load time, not during execution.

### 2. SDN Format (Not Binary)

**Rationale:** Human-readable, debuggable, extensible. Easy to inspect and modify manually for debugging.

**Trade-off:** Larger size than binary format. Acceptable because note.sdn is relatively small metadata.

### 3. Reuse SectionType::TemplateMeta

**Rationale:** Avoids extending the SectionType enum, which would require SMF version bump.

**Trade-off:** Section type is ambiguous (could be metadata or note.sdn). Resolved by checking section name field.

### 4. Terminator Design: `\n# END_NOTE\n`

**Rationale:**
- SDN comment syntax (starts with #)
- Easy to scan for (unique marker)
- Human-readable when inspecting files

**Alternative considered:** Binary magic number (rejected for consistency with SDN format)

## Benefits

1. **Lazy Instantiation**: Link/load-time instantiation reduces compile-time bloat
2. **Dependency Tracking**: Enables circular dependency detection
3. **Hot-Reload**: Update instantiations without full rebuild
4. **Debuggability**: Human-readable SDN format
5. **Flexibility**: Zero-size trick allows dynamic growth

## Limitations

1. **No SDN Parser Yet**: Phase 2 (reading) not yet implemented
2. **No Compile-Time Integration**: Phase 3 (tracking) not yet implemented
3. **Section Type Ambiguity**: Uses TemplateMeta type for both metadata and note.sdn
4. **No Size Validation**: Could overflow into next section (mitigated in Phase 7)

## Files Modified/Created

### Rust
- **Created:** `src/rust/compiler/src/monomorphize/note_sdn.rs` (407 lines)
- **Modified:** `src/rust/compiler/src/monomorphize/mod.rs` (added exports)
- **Modified:** `src/rust/compiler/src/smf_writer.rs` (added note.sdn section writing)

### Simple
- **Created:** `simple/compiler/monomorphize/note_sdn.spl` (387 lines)
- **Modified:** `simple/compiler/monomorphize/mod.spl` (added export)
- **Modified:** `simple/compiler/smf_writer.spl` (added note.sdn section writing)

### Tests
- **Created:** `test/lib/std/unit/compiler/note_sdn_spec.spl` (13 test cases)

### Documentation
- **Created:** `doc/design/smf_note_sdn_implementation.md` (this file)

## Success Metrics

✅ note.sdn section written with size=0
✅ Instantiation entries tracked in note.sdn
✅ SDN format serialization working
✅ Zero-size trick implemented
✅ Terminator `\n# END_NOTE\n` added
✅ Rust implementation complete
✅ Simple implementation complete
✅ Unit tests passing

⏳ SDN parsing (Phase 2)
⏳ Compile-time tracking (Phase 3)
⏳ Link-time lazy instantiation (Phase 4)
⏳ Load-time JIT instantiation (Phase 5)
⏳ Circular dependency detection (Phase 6)
⏳ Hot-reload support (Phase 7)

## Conclusion

Phase 1 of the SMF note.sdn implementation is complete. The infrastructure for tracking instantiation metadata is in place in both Rust and Simple. The zero-size section trick enables hot-reload updates, and the SDN format provides human-readable metadata for debugging and tooling.

Next steps are to implement the loader (Phase 2) and integrate with the monomorphization engine (Phase 3).
