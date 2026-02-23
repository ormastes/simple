# SMF note.sdn Usage Guide

## Overview

The `note.sdn` section in SMF files tracks generic instantiation metadata to enable:
- **Lazy instantiation** at link-time and load-time
- **Circular dependency detection** for template instantiations
- **Hot-reload support** for dynamic code updates
- **Type inference tracking** for debugging and analysis

## Quick Start

### Rust API

```rust
use simple_compiler::monomorphize::{
    NoteSdnMetadata, InstantiationEntry, InstantiationStatus,
    DependencyEdge, DependencyKind, ConcreteType
};

// 1. Create metadata container
let mut note = NoteSdnMetadata::new();

// 2. Track a template instantiation
note.add_instantiation(InstantiationEntry::new(
    "List".to_string(),                                    // Template name
    vec![ConcreteType::Named("Int".to_string())],          // Type arguments
    "List$Int".to_string(),                                // Mangled name
    "app.spl".to_string(),                                 // Source file
    "app.spl:10:5".to_string(),                            // Location
    "app.o".to_string(),                                   // Object file
    InstantiationStatus::Compiled,                         // Status
));

// 3. Track dependency
note.add_dependency(DependencyEdge::new(
    "List$Int".to_string(),                                // From
    "Int".to_string(),                                     // To
    DependencyKind::TypeParam,                             // Kind
));

// 4. Serialize to SDN format
let sdn_text = note.to_sdn();
println!("{}", sdn_text);
```

### Simple API

```simple
use simple/compiler/monomorphize/note_sdn.*
use simple/compiler/monomorphize/metadata.ConcreteType

# 1. Create metadata container
var note = NoteSdnMetadata.new()

# 2. Track a template instantiation
note.add_instantiation(InstantiationEntry.new(
    template: "List",
    type_args: [ConcreteType.Named("Int", [])],
    mangled_name: "List$Int",
    from_file: "app.spl",
    from_loc: "app.spl:10:5",
    to_obj: "app.o",
    status: InstantiationStatus.Compiled
))

# 3. Track dependency
note.add_dependency(DependencyEdge.new(
    from_inst: "List$Int",
    to_inst: "Int",
    dep_kind: DependencyKind.TypeParam
))

# 4. Serialize to SDN format
val sdn_text = note.to_sdn()
print sdn_text
```

## Core Concepts

### 1. Instantiation Tracking

Track which generic templates were instantiated and with what type arguments:

```rust
// Generic function: fn identity<T>(x: T) -> T
// Instantiation: identity(42)  // T = Int

note.add_instantiation(InstantiationEntry::new(
    "identity".to_string(),
    vec![ConcreteType::Named("Int".to_string())],
    "identity$Int".to_string(),
    "main.spl".to_string(),
    "main.spl:15:10".to_string(),
    "main.o".to_string(),
    InstantiationStatus::Compiled,
));
```

### 2. Possible Instantiations

Track instantiations that *could* be generated lazily:

```rust
// Library provides List<T> but only List<Int> was used
// List<String> could be generated on-demand if needed

note.add_possible(PossibleInstantiationEntry::new(
    "List".to_string(),
    vec![ConcreteType::Named("String".to_string())],
    "List$String".to_string(),
    "string_processing_module".to_string(),
    true,  // can_defer
));
```

### 3. Type Inference Tracking

Track type inference events for debugging:

```rust
// val x = 42  // Type inferred as Int

note.add_type_inference(TypeInferenceEntry::new(
    "Int".to_string(),          // Inferred type
    "42".to_string(),            // Expression
    "literal".to_string(),       // Context
    "app.spl".to_string(),       // File
    "app.spl:5:10".to_string(),  // Location
));
```

### 4. Dependency Graph

Track dependencies between instantiations:

```rust
// struct Container<T> { item: T }
// Container<List<Int>> depends on List<Int>

note.add_dependency(DependencyEdge::new(
    "Container$List$Int".to_string(),
    "List$Int".to_string(),
    DependencyKind::FieldType,
));
```

### 5. Circular Dependency Detection

Track circular dependencies (warnings or errors):

```rust
// Soft cycle (warning): Node<T> -> Option<Node<T>> -> Node<T>
note.add_circular_warning(CircularWarning::new(
    "Node$T->Option$Node$T->Node$T".to_string(),
    "warning".to_string(),
));

// Hard cycle (error): A<T> -> B<T> -> C<T> -> A<T>
note.add_circular_error(CircularError::new(
    "A$T->B$T->C$T->A$T".to_string(),
    "E0420".to_string(),
));
```

## Data Structures

### NoteSdnMetadata

Main container for all instantiation metadata:

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
- `new()` - Create empty metadata
- `is_empty()` - Check if empty
- `add_instantiation(entry)` - Add instantiation
- `add_possible(entry)` - Add possible instantiation
- `add_type_inference(entry)` - Add type inference
- `add_dependency(edge)` - Add dependency
- `add_circular_warning(warning)` - Add warning
- `add_circular_error(error)` - Add error
- `to_sdn()` - Serialize to SDN format

### InstantiationEntry

Tracks a compiled template instantiation:

```rust
pub struct InstantiationEntry {
    pub template: String,        // "List", "Option", "identity"
    pub type_args: String,        // "Int", "String,Float"
    pub mangled_name: String,     // "List$Int", "identity$Float"
    pub from_file: String,        // Source file
    pub from_loc: String,         // "file:line:col"
    pub to_obj: String,           // Object file
    pub status: InstantiationStatus,
}
```

### InstantiationStatus

```rust
pub enum InstantiationStatus {
    Compiled,      // Compiled to native code
    Deferred,      // Deferred for lazy compilation
    JitCompiled,   // JIT-compiled at runtime
}
```

### DependencyKind

```rust
pub enum DependencyKind {
    TypeParam,    // Type parameter: List<T> depends on T
    FieldType,    // Field type: struct has field of type T
    InnerType,    // Inner type: Option<T> wraps T
    MethodDep,    // Method dependency: method returns T
}
```

## SDN Format

The note.sdn section uses human-readable SDN format:

```sdn
# Instantiation To/From Metadata
# Format version: 1.0

# Template instantiations (what was compiled)
instantiations |id, template, type_args, mangled_name, from_file, from_loc, to_obj, status|
    0, "List", "Int", "List$Int", "app.spl", "app.spl:10:5", "app.o", "compiled"
    1, "Option", "String", "Option$String", "lib.spl", "lib.spl:42:3", "lib.o", "compiled"

# Possible instantiations (can be lazily generated)
possible |id, template, type_args, mangled_name, required_by, can_defer|
    0, "List", "Float", "List$Float", "math_module", true
    1, "Result", "Int,text", "Result$Int$text", "io_module", true

# Type inference instantiations
type_inferences |id, inferred_type, expr, context, from_file, from_loc|
    0, "Int", "42", "literal", "app.spl", "app.spl:5:10"
    1, "[Int]", "[1,2,3]", "array_literal", "app.spl", "app.spl:6:12"

# Instantiation graph (to/from relationships)
dependencies |from_inst, to_inst, dep_kind|
    "List$Int", "Int", "type_param"
    "Option$String", "String", "type_param"
    "Result$Int$text", "Int", "type_param"
    "Result$Int$text", "text", "type_param"

# Circular dependency detection results
circular_warnings |id, cycle_path, severity|
    0, "Node$T->Option$Node$T->Node$T", "warning"

circular_errors |id, cycle_path, error_code|

# END_NOTE
```

## Integration with SMF Writer

### Rust

```rust
use simple_compiler::smf_writer::generate_smf_with_all_sections;

let smf_bytes = generate_smf_with_all_sections(
    &object_code,
    Some(&templates),      // Generic templates
    Some(&metadata),       // Monomorphization metadata
    Some(&note_sdn),       // ⭐ note.sdn metadata
    None,                  // GC allocator
    target,
);
```

### Simple

```simple
use simple/compiler/smf_writer.generate_smf_with_all_sections

val smf_bytes = generate_smf_with_all_sections(
    object_code: object_code,
    templates: Some(templates),
    metadata: Some(metadata),
    note_sdn: Some(note_sdn),  # ⭐ note.sdn metadata
    target: target
)
```

## Common Patterns

### Pattern 1: Track Single Instantiation

```rust
fn track_instantiation(
    note: &mut NoteSdnMetadata,
    template: &str,
    type_args: Vec<ConcreteType>,
    location: &str,
) {
    let mangled = format!("{}${}", template,
        type_args.iter()
            .map(|t| t.to_string())
            .collect::<Vec<_>>()
            .join("$")
    );

    note.add_instantiation(InstantiationEntry::new(
        template.to_string(),
        type_args,
        mangled,
        location.to_string(),
        location.to_string(),
        "output.o".to_string(),
        InstantiationStatus::Compiled,
    ));
}

// Usage
track_instantiation(&mut note, "List", vec![ConcreteType::Int], "app.spl:10:5");
```

### Pattern 2: Build Dependency Graph

```rust
fn build_dependency_graph(note: &mut NoteSdnMetadata) {
    // For Container<List<Int>>:
    // Container$List$Int -> List$Int (field type)
    note.add_dependency(DependencyEdge::new(
        "Container$List$Int".to_string(),
        "List$Int".to_string(),
        DependencyKind::FieldType,
    ));

    // List$Int -> Int (type param)
    note.add_dependency(DependencyEdge::new(
        "List$Int".to_string(),
        "Int".to_string(),
        DependencyKind::TypeParam,
    ));
}
```

### Pattern 3: Track All Instantiations in Module

```rust
fn track_module_instantiations(
    note: &mut NoteSdnMetadata,
    instantiations: &[(&str, Vec<ConcreteType>)],
    module: &str,
) {
    for (template, type_args) in instantiations {
        let mangled = format!("{}${}", template,
            type_args.iter()
                .map(|t| t.to_string())
                .collect::<Vec<_>>()
                .join("$")
        );

        note.add_instantiation(InstantiationEntry::new(
            template.to_string(),
            type_args.clone(),
            mangled,
            format!("{}.spl", module),
            format!("{}.spl:0:0", module),
            format!("{}.o", module),
            InstantiationStatus::Compiled,
        ));
    }
}

// Usage
track_module_instantiations(&mut note, &[
    ("List", vec![ConcreteType::Int]),
    ("Option", vec![ConcreteType::String]),
    ("Result", vec![ConcreteType::Int, ConcreteType::String]),
], "myapp");
```

## Debugging

### View SDN Output

```rust
let note = NoteSdnMetadata::new();
// ... add entries ...
println!("{}", note.to_sdn());
```

Output:
```sdn
# Instantiation To/From Metadata
# Format version: 1.0
...
```

### Check if Empty

```rust
if note.is_empty() {
    println!("No instantiations tracked");
} else {
    println!("Tracked {} instantiations", note.instantiations.len());
}
```

### Count Entries

```rust
println!("Instantiations: {}", note.instantiations.len());
println!("Possible: {}", note.possible.len());
println!("Dependencies: {}", note.dependencies.len());
println!("Warnings: {}", note.circular_warnings.len());
println!("Errors: {}", note.circular_errors.len());
```

## Best Practices

### 1. Always Track Dependencies

When adding an instantiation, also add its dependencies:

```rust
// Add instantiation
note.add_instantiation(entry_for_list_int);

// Add dependency
note.add_dependency(DependencyEdge::new(
    "List$Int".to_string(),
    "Int".to_string(),
    DependencyKind::TypeParam,
));
```

### 2. Use Descriptive Locations

Always include file:line:col for debugging:

```rust
// Good
from_loc: "app.spl:42:15"

// Bad
from_loc: "app.spl"
```

### 3. Mark Deferrable Instantiations

Only mark instantiations as deferrable if safe:

```rust
note.add_possible(PossibleInstantiationEntry::new(
    // ...
    can_defer: !has_side_effects && !is_critical_path,
));
```

### 4. Track Type Inferences

Track type inferences for better error messages:

```rust
note.add_type_inference(TypeInferenceEntry::new(
    inferred_type: "Int".to_string(),
    expr: "x + 1".to_string(),
    context: "binary_op".to_string(),
    from_file: location.file,
    from_loc: location.to_string(),
));
```

## Error Codes

- **E0420** - Hard circular dependency in template instantiation
- **E0421** - Circular dependency in type inference

## Future Features

### Phase 2: Reading note.sdn
- Load note.sdn from SMF files
- Parse SDN format
- Build dependency graph

### Phase 3: Compile-Time Integration
- Auto-track instantiations during compilation
- Auto-detect circular dependencies
- Auto-populate possible instantiations

### Phase 4: Link-Time Lazy Instantiation
- Generate missing instantiations from `possible` table
- Merge note.sdn from multiple object files
- Resolve cross-module dependencies

### Phase 5: Hot-Reload
- Update note.sdn dynamically
- Track JIT-compiled instantiations
- Invalidate stale entries

## References

- [SMF note.sdn Implementation](../design/smf_note_sdn_implementation.md)
- [Monomorphization Guide](monomorphization_guide.md)
- [SMF Format Specification](smf_format_spec.md)
