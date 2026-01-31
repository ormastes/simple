// Example usage of note.sdn API
//
// This example demonstrates how to use the note.sdn API to track
// generic instantiation metadata.
//
// Run with: cargo run --example note_sdn_example

use simple_compiler::monomorphize::{
    CircularError, CircularWarning, ConcreteType, DependencyEdge, DependencyKind,
    InstantiationEntry, InstantiationStatus, NoteSdnMetadata, PossibleInstantiationEntry,
    TypeInferenceEntry,
};

fn main() {
    println!("=== note.sdn Example ===\n");

    // Create metadata container
    let mut note = NoteSdnMetadata::new();
    println!("✓ Created empty NoteSdnMetadata");

    // Example 1: Track a simple instantiation (List<Int>)
    println!("\n--- Example 1: Track List<Int> instantiation ---");
    note.add_instantiation(InstantiationEntry::new(
        "List".to_string(),
        vec![ConcreteType::Named("Int".to_string(), vec![])],
        "List$Int".to_string(),
        "app.spl".to_string(),
        "app.spl:10:5".to_string(),
        "app.o".to_string(),
        InstantiationStatus::Compiled,
    ));
    println!("✓ Added List<Int> instantiation");

    // Example 2: Track dependency (List<Int> depends on Int)
    println!("\n--- Example 2: Track dependency ---");
    note.add_dependency(DependencyEdge::new(
        "List$Int".to_string(),
        "Int".to_string(),
        DependencyKind::TypeParam,
    ));
    println!("✓ Added dependency: List<Int> -> Int");

    // Example 3: Track possible future instantiation (Option<String>)
    println!("\n--- Example 3: Track possible instantiation ---");
    note.add_possible(PossibleInstantiationEntry::new(
        "Option".to_string(),
        vec![ConcreteType::Named("String".to_string(), vec![])],
        "Option$String".to_string(),
        "string_module".to_string(),
        true,
    ));
    println!("✓ Added possible: Option<String>");

    // Example 4: Track type inference
    println!("\n--- Example 4: Track type inference ---");
    note.add_type_inference(TypeInferenceEntry::new(
        "Int".to_string(),
        "42".to_string(),
        "literal".to_string(),
        "app.spl".to_string(),
        "app.spl:5:10".to_string(),
    ));
    println!("✓ Added type inference: 42 -> Int");

    // Example 5: Track circular warning
    println!("\n--- Example 5: Track circular dependency warning ---");
    note.add_circular_warning(CircularWarning::new(
        "Node$T->Option$Node$T->Node$T".to_string(),
        "warning".to_string(),
    ));
    println!("✓ Added circular warning");

    // Example 6: Serialize to SDN format
    println!("\n--- Example 6: Serialize to SDN ---");
    let sdn = note.to_sdn();
    println!("✓ Serialized to SDN format\n");
    println!("SDN Output:");
    println!("{}", "=".repeat(60));
    println!("{}", sdn);
    println!("{}", "=".repeat(60));

    // Example 7: Summary statistics
    println!("\n--- Summary Statistics ---");
    println!("Instantiations: {}", note.instantiations.len());
    println!("Possible:       {}", note.possible.len());
    println!("Inferences:     {}", note.type_inferences.len());
    println!("Dependencies:   {}", note.dependencies.len());
    println!("Warnings:       {}", note.circular_warnings.len());
    println!("Errors:         {}", note.circular_errors.len());
    println!("Is empty:       {}", note.is_empty());

    println!("\n✓ All examples completed successfully!");
}
