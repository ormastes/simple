# note.sdn API Reference

## Module: `simple_compiler::monomorphize::note_sdn`

Rust API for note.sdn instantiation metadata tracking.

---

## Data Structures

### `NoteSdnMetadata`

**Description:** Complete note.sdn metadata for an SMF file.

```rust
pub struct NoteSdnMetadata {
    pub instantiations: Vec<InstantiationEntry>,
    pub possible: Vec<PossibleInstantiationEntry>,
    pub type_inferences: Vec<TypeInferenceEntry>,
    pub dependencies: Vec<DependencyEdge>,
    pub circular_warnings: Vec<CircularWarning>,
    pub circular_errors: Vec<CircularError>,
}
```

**Methods:**

#### `new() -> Self`
Create a new empty metadata collection.

```rust
let note = NoteSdnMetadata::new();
assert!(note.is_empty());
```

#### `is_empty(&self) -> bool`
Check if metadata is empty (no entries in any table).

```rust
let note = NoteSdnMetadata::new();
assert!(note.is_empty());
```

#### `add_instantiation(&mut self, entry: InstantiationEntry)`
Add an instantiation entry to the `instantiations` table.

```rust
note.add_instantiation(InstantiationEntry::new(
    "List".to_string(),
    vec![ConcreteType::Named("Int".to_string())],
    "List$Int".to_string(),
    "app.spl".to_string(),
    "app.spl:10:5".to_string(),
    "app.o".to_string(),
    InstantiationStatus::Compiled,
));
```

#### `add_possible(&mut self, entry: PossibleInstantiationEntry)`
Add a possible instantiation entry to the `possible` table.

```rust
note.add_possible(PossibleInstantiationEntry::new(
    "Option".to_string(),
    vec![ConcreteType::Named("Float".to_string())],
    "Option$Float".to_string(),
    "math_module".to_string(),
    true,
));
```

#### `add_type_inference(&mut self, entry: TypeInferenceEntry)`
Add a type inference entry to the `type_inferences` table.

```rust
note.add_type_inference(TypeInferenceEntry::new(
    "Int".to_string(),
    "42".to_string(),
    "literal".to_string(),
    "app.spl".to_string(),
    "app.spl:5:10".to_string(),
));
```

#### `add_dependency(&mut self, edge: DependencyEdge)`
Add a dependency edge to the `dependencies` table.

```rust
note.add_dependency(DependencyEdge::new(
    "List$Int".to_string(),
    "Int".to_string(),
    DependencyKind::TypeParam,
));
```

#### `add_circular_warning(&mut self, warning: CircularWarning)`
Add a circular dependency warning to the `circular_warnings` table.

```rust
note.add_circular_warning(CircularWarning::new(
    "Node$T->Option$Node$T->Node$T".to_string(),
    "warning".to_string(),
));
```

#### `add_circular_error(&mut self, error: CircularError)`
Add a circular dependency error to the `circular_errors` table.

```rust
note.add_circular_error(CircularError::new(
    "A$T->B$T->C$T->A$T".to_string(),
    "E0420".to_string(),
));
```

#### `to_sdn(&self) -> String`
Serialize to SDN format with terminator.

Returns a string containing the complete SDN representation with all tables and terminator `\n# END_NOTE\n`.

```rust
let sdn = note.to_sdn();
assert!(sdn.contains("# END_NOTE\n"));
```

#### `from_sdn(content: &str) -> Result<Self, String>`
Parse from SDN format.

**Status:** Not yet implemented (Phase 2)

```rust
let result = NoteSdnMetadata::from_sdn(content);
// Currently returns Err("SDN parsing not yet implemented")
```

---

### `InstantiationEntry`

**Description:** A template instantiation that was compiled.

```rust
pub struct InstantiationEntry {
    pub template: String,
    pub type_args: String,
    pub mangled_name: String,
    pub from_file: String,
    pub from_loc: String,
    pub to_obj: String,
    pub status: InstantiationStatus,
}
```

**Constructor:**

#### `new(...) -> Self`
Create a new instantiation entry.

```rust
pub fn new(
    template: String,
    type_args: Vec<ConcreteType>,
    mangled_name: String,
    from_file: String,
    from_loc: String,
    to_obj: String,
    status: InstantiationStatus,
) -> Self
```

**Parameters:**
- `template` - Base template name (e.g., "List", "Option")
- `type_args` - Concrete type arguments (converted to comma-separated string)
- `mangled_name` - Mangled symbol name (e.g., "List$Int")
- `from_file` - Source file that triggered instantiation
- `from_loc` - Source location in format "file:line:col"
- `to_obj` - Object file where compiled code resides
- `status` - Compilation status

**Example:**
```rust
let entry = InstantiationEntry::new(
    "identity".to_string(),
    vec![ConcreteType::Named("Int".to_string())],
    "identity$Int".to_string(),
    "main.spl".to_string(),
    "main.spl:15:10".to_string(),
    "main.o".to_string(),
    InstantiationStatus::Compiled,
);
```

---

### `InstantiationStatus`

**Description:** Compilation status for an instantiation.

```rust
pub enum InstantiationStatus {
    Compiled,      // Compiled to native code
    Deferred,      // Deferred for lazy compilation
    JitCompiled,   // JIT-compiled at runtime
}
```

**Methods:**

#### `as_str(&self) -> &'static str`
Convert to string representation.

```rust
assert_eq!(InstantiationStatus::Compiled.as_str(), "compiled");
assert_eq!(InstantiationStatus::Deferred.as_str(), "deferred");
assert_eq!(InstantiationStatus::JitCompiled.as_str(), "jit_compiled");
```

#### `from_str(s: &str) -> Result<Self, String>`
Parse from string representation.

```rust
let status = InstantiationStatus::from_str("compiled")?;
assert_eq!(status, InstantiationStatus::Compiled);
```

---

### `PossibleInstantiationEntry`

**Description:** A possible instantiation that can be generated on-demand.

```rust
pub struct PossibleInstantiationEntry {
    pub template: String,
    pub type_args: String,
    pub mangled_name: String,
    pub required_by: String,
    pub can_defer: bool,
}
```

**Constructor:**

#### `new(...) -> Self`
Create a new possible instantiation entry.

```rust
pub fn new(
    template: String,
    type_args: Vec<ConcreteType>,
    mangled_name: String,
    required_by: String,
    can_defer: bool,
) -> Self
```

**Parameters:**
- `template` - Base template name
- `type_args` - Concrete type arguments
- `mangled_name` - Mangled symbol name
- `required_by` - Which module needs this instantiation
- `can_defer` - Can this be deferred to link/load time?

---

### `TypeInferenceEntry`

**Description:** A type inference event.

```rust
pub struct TypeInferenceEntry {
    pub inferred_type: String,
    pub expr: String,
    pub context: String,
    pub from_file: String,
    pub from_loc: String,
}
```

**Constructor:**

#### `new(...) -> Self`
Create a new type inference entry.

```rust
pub fn new(
    inferred_type: String,
    expr: String,
    context: String,
    from_file: String,
    from_loc: String,
) -> Self
```

**Parameters:**
- `inferred_type` - Inferred type (may be placeholder like "?T")
- `expr` - Expression text
- `context` - Inference context (e.g., "literal", "var_init")
- `from_file` - Source file
- `from_loc` - Source location in format "file:line:col"

---

### `DependencyEdge`

**Description:** A dependency edge in the instantiation graph.

```rust
pub struct DependencyEdge {
    pub from_inst: String,
    pub to_inst: String,
    pub dep_kind: DependencyKind,
}
```

**Constructor:**

#### `new(from_inst: String, to_inst: String, dep_kind: DependencyKind) -> Self`
Create a new dependency edge.

```rust
let edge = DependencyEdge::new(
    "Container$List$Int".to_string(),
    "List$Int".to_string(),
    DependencyKind::FieldType,
);
```

---

### `DependencyKind`

**Description:** Kind of dependency between instantiations.

```rust
pub enum DependencyKind {
    TypeParam,    // Type parameter dependency
    FieldType,    // Field type dependency
    InnerType,    // Inner type dependency
    MethodDep,    // Method dependency
}
```

**Methods:**

#### `as_str(&self) -> &'static str`
Convert to string representation.

```rust
assert_eq!(DependencyKind::TypeParam.as_str(), "type_param");
assert_eq!(DependencyKind::FieldType.as_str(), "field_type");
```

#### `from_str(s: &str) -> Result<Self, String>`
Parse from string representation.

```rust
let kind = DependencyKind::from_str("type_param")?;
assert_eq!(kind, DependencyKind::TypeParam);
```

---

### `CircularWarning`

**Description:** A circular dependency warning (soft cycle, broken by indirection).

```rust
pub struct CircularWarning {
    pub cycle_path: String,
    pub severity: String,
}
```

**Constructor:**

#### `new(cycle_path: String, severity: String) -> Self`
Create a new circular warning.

```rust
let warning = CircularWarning::new(
    "Node$T->Option$Node$T->Node$T".to_string(),
    "warning".to_string(),
);
```

---

### `CircularError`

**Description:** A circular dependency error (hard cycle, not allowed).

```rust
pub struct CircularError {
    pub cycle_path: String,
    pub error_code: String,
}
```

**Constructor:**

#### `new(cycle_path: String, error_code: String) -> Self`
Create a new circular error.

```rust
let error = CircularError::new(
    "A$T->B$T->C$T->A$T".to_string(),
    "E0420".to_string(),
);
```

---

## Module: `simple/compiler/monomorphize/note_sdn`

Simple API for note.sdn instantiation metadata tracking.

### Differences from Rust API

The Simple API is nearly identical to the Rust API with these differences:

1. **Constructors:** Use `static fn new()` instead of associated functions
2. **Methods:** Use `me` keyword for mutating methods
3. **Types:** Use Simple types (`text`, `bool`, `[T]`, etc.)
4. **Results:** Use Simple `Result<T, E>` type

### Example

```simple
use simple/compiler/monomorphize/note_sdn.*

# Create metadata
var note = NoteSdnMetadata.new()

# Add entry
note.add_instantiation(InstantiationEntry.new(
    template: "List",
    type_args: [ConcreteType.Named("Int", [])],
    mangled_name: "List$Int",
    from_file: "app.spl",
    from_loc: "app.spl:10:5",
    to_obj: "app.o",
    status: InstantiationStatus.Compiled
))

# Serialize
val sdn = note.to_sdn()
```

---

## SDN Format Specification

### Structure

```sdn
# Instantiation To/From Metadata
# Format version: 1.0

<table_name> |column1, column2, ...|
    value1, value2, ...
    value1, value2, ...

# END_NOTE
```

### Tables

#### `instantiations`
Columns: `id, template, type_args, mangled_name, from_file, from_loc, to_obj, status`

#### `possible`
Columns: `id, template, type_args, mangled_name, required_by, can_defer`

#### `type_inferences`
Columns: `id, inferred_type, expr, context, from_file, from_loc`

#### `dependencies`
Columns: `from_inst, to_inst, dep_kind`

#### `circular_warnings`
Columns: `id, cycle_path, severity`

#### `circular_errors`
Columns: `id, cycle_path, error_code`

### Escaping Rules

Special characters are escaped as follows:
- `\` → `\\`
- `"` → `\"`
- `\n` → `\\n`
- `\r` → `\\r`
- `\t` → `\\t`

---

## Integration

### SMF Writer

Include note.sdn in SMF file generation:

**Rust:**
```rust
use simple_compiler::smf_writer::generate_smf_with_all_sections;

let smf = generate_smf_with_all_sections(
    &object_code,
    Some(&templates),
    Some(&metadata),
    Some(&note_sdn),  // ⭐ note.sdn section
    None,
    target,
);
```

**Simple:**
```simple
use simple/compiler/smf_writer.generate_smf_with_all_sections

val smf = generate_smf_with_all_sections(
    object_code: code,
    templates: Some(templates),
    metadata: Some(metadata),
    note_sdn: Some(note_sdn),  # ⭐ note.sdn section
    target: target
)
```

### Section Properties

The note.sdn section in SMF files has these properties:
- **Name:** `"note.sdn"` (16-byte field)
- **Type:** `SectionType::TemplateMeta` (13)
- **Size:** `0` (zero-size trick)
- **Flags:** `SECTION_FLAG_READ` (0x01)
- **Alignment:** `1`

### Zero-Size Mechanism

The section table shows `size: 0`, but actual data is terminated with `\n# END_NOTE\n`. Loaders must scan for the terminator to determine actual size.

---

## Error Codes

### E0420: Circular Template Dependency

Hard circular dependency in template instantiation. Not allowed.

**Example:**
```
A<T> contains field of type B<T>
B<T> contains field of type C<T>
C<T> contains field of type A<T>

→ Cycle: A<T> -> B<T> -> C<T> -> A<T>
```

### E0421: Circular Type Inference

Circular dependency in type inference. Not allowed.

**Example:**
```
val x = y + 1
val y = x * 2

→ Type of x depends on type of y, type of y depends on type of x
```

---

## See Also

- [note.sdn Usage Guide](../guide/note_sdn_usage_guide.md)
- [SMF Format Specification](smf_format_spec.md)
- [Monomorphization Guide](../guide/monomorphization_guide.md)
