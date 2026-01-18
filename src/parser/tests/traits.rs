use simple_parser::ast::Node;
use simple_parser::Parser;

fn parse(src: &str) -> Vec<Node> {
    let mut parser = Parser::new(src);
    let module = parser.parse().expect("parse ok");
    module.items
}

fn parse_ok(src: &str) {
    let mut parser = Parser::new(src);
    parser.parse().expect("should parse");
}

// Trait definitions
#[test]
fn parse_trait_definition() {
    let items = parse("trait Show:\n    fn show(self):\n        return 0");
    if let Node::Trait(t) = &items[0] {
        assert_eq!(t.name, "Show");
    } else {
        panic!("expected trait");
    }
}

#[test]
fn parse_trait_where_clause() {
    parse_ok("trait Comparable<T> where T: Ord:\n    fn compare(self, other: T) -> i64:\n        return 0");
}

// Trait implementations
#[test]
fn parse_trait_impl() {
    parse_ok("impl Show for Point:\n    fn show(self):\n        return 0");
}

#[test]
fn parse_default_trait_impl_attribute() {
    let items = parse("#[default]\nimpl[T] Process for T:\n    fn process(self):\n        return 0");
    if let Node::Impl(impl_block) = &items[0] {
        assert!(impl_block.attributes.iter().any(|attr| attr.name == "default"));
    } else {
        panic!("Expected impl block");
    }
}

// Default trait implementation tests
#[test]
fn parse_trait_abstract_method() {
    // Trait with abstract method (no body)
    let items = parse("trait Greet:\n    fn greet(self) -> str");
    if let Node::Trait(t) = &items[0] {
        assert_eq!(t.methods.len(), 1);
        assert!(t.methods[0].is_abstract);
        assert_eq!(t.methods[0].name, "greet");
    } else {
        panic!("Expected trait");
    }
}

#[test]
fn parse_trait_default_method() {
    // Trait with default implementation
    let items = parse("trait Greet:\n    fn greet(self) -> str:\n        return 'Hello'");
    if let Node::Trait(t) = &items[0] {
        assert_eq!(t.methods.len(), 1);
        assert!(!t.methods[0].is_abstract);
        assert_eq!(t.methods[0].name, "greet");
    } else {
        panic!("Expected trait");
    }
}

#[test]
fn parse_trait_mixed_methods() {
    // Trait with both abstract and default methods
    let items = parse("trait Animal:\n    fn speak(self) -> str\n    fn sleep(self):\n        return 0");
    if let Node::Trait(t) = &items[0] {
        assert_eq!(t.methods.len(), 2);
        // speak is abstract (no body)
        assert!(t.methods[0].is_abstract);
        assert_eq!(t.methods[0].name, "speak");
        // sleep has default implementation
        assert!(!t.methods[1].is_abstract);
        assert_eq!(t.methods[1].name, "sleep");
    } else {
        panic!("Expected trait");
    }
}

// Associated types tests
#[test]
fn parse_trait_associated_type_simple() {
    // Trait with simple associated type
    let items = parse("trait Iterator:\n    type Item\n    fn next(self) -> Item");
    if let Node::Trait(t) = &items[0] {
        assert_eq!(t.name, "Iterator");
        assert_eq!(t.associated_types.len(), 1);
        assert_eq!(t.associated_types[0].name, "Item");
        assert!(t.associated_types[0].bounds.is_empty());
        assert!(t.associated_types[0].default.is_none());
        assert_eq!(t.methods.len(), 1);
    } else {
        panic!("Expected trait");
    }
}

#[test]
fn parse_trait_associated_type_with_bounds() {
    // Associated type with trait bounds
    let items = parse("trait Collection:\n    type Item: Clone + Default\n    fn get(self) -> Item");
    if let Node::Trait(t) = &items[0] {
        assert_eq!(t.associated_types.len(), 1);
        assert_eq!(t.associated_types[0].name, "Item");
        assert_eq!(t.associated_types[0].bounds, vec!["Clone", "Default"]);
    } else {
        panic!("Expected trait");
    }
}

#[test]
fn parse_trait_associated_type_with_default() {
    // Associated type with default type
    let items = parse("trait Container:\n    type Item = i64\n    fn get(self) -> Item");
    if let Node::Trait(t) = &items[0] {
        assert_eq!(t.associated_types.len(), 1);
        assert_eq!(t.associated_types[0].name, "Item");
        assert!(t.associated_types[0].default.is_some());
    } else {
        panic!("Expected trait");
    }
}

#[test]
fn parse_impl_associated_type() {
    // Impl block with associated type implementation
    let items = parse("impl Iterator for List:\n    type Item = i64\n    fn next(self) -> i64:\n        return 0");
    if let Node::Impl(impl_block) = &items[0] {
        assert_eq!(impl_block.associated_types.len(), 1);
        assert_eq!(impl_block.associated_types[0].name, "Item");
        assert_eq!(impl_block.methods.len(), 1);
    } else {
        panic!("Expected impl block");
    }
}

#[test]
fn parse_trait_multiple_associated_types() {
    // Multiple associated types
    let items = parse("trait Map:\n    type Key\n    type Value\n    fn get(self, k: Key) -> Value");
    if let Node::Trait(t) = &items[0] {
        assert_eq!(t.associated_types.len(), 2);
        assert_eq!(t.associated_types[0].name, "Key");
        assert_eq!(t.associated_types[1].name, "Value");
    } else {
        panic!("Expected trait");
    }
}

// Interface binding tests (static polymorphism)
#[test]
fn parse_interface_binding() {
    // Basic interface binding for static dispatch
    let items = parse("bind Logger = ConsoleLogger");
    if let Node::InterfaceBinding(binding) = &items[0] {
        assert_eq!(binding.interface_name, "Logger");
    } else {
        panic!("Expected interface binding");
    }
}

#[test]
fn parse_interface_binding_generic_type() {
    // Binding with generic implementation type
    let items = parse("bind Serializer = JsonSerializer[String]");
    if let Node::InterfaceBinding(binding) = &items[0] {
        assert_eq!(binding.interface_name, "Serializer");
    } else {
        panic!("Expected interface binding");
    }
}

// Trait inheritance tests
#[test]
fn parse_trait_simple_inheritance() {
    // Simple trait inheritance: trait Copy: Clone
    use simple_parser::ast::Type;
    let items = parse("trait Copy: Clone:\n    fn copy(self) -> Self");
    if let Node::Trait(t) = &items[0] {
        assert_eq!(t.name, "Copy");
        assert_eq!(t.super_traits.len(), 1);
        assert_eq!(t.super_traits[0], Type::Simple("Clone".to_string()));
    } else {
        panic!("Expected trait");
    }
}

#[test]
fn parse_trait_generic_inheritance() {
    // Generic trait inheritance: trait Sequence<T>: Collection<T>
    use simple_parser::ast::Type;
    let items = parse("trait Sequence<T>: Collection<T>:\n    fn len(self) -> usize");
    if let Node::Trait(t) = &items[0] {
        assert_eq!(t.name, "Sequence");
        assert_eq!(t.generic_params, vec!["T"]);
        assert_eq!(t.super_traits.len(), 1);
        // Check it's a generic type Collection<T>
        match &t.super_traits[0] {
            Type::Generic { name, args } => {
                assert_eq!(name, "Collection");
                assert_eq!(args.len(), 1);
            }
            _ => panic!("Expected generic super trait, got {:?}", t.super_traits[0]),
        }
    } else {
        panic!("Expected trait");
    }
}

#[test]
fn parse_trait_multiple_inheritance() {
    // Multiple trait inheritance: trait Debug: Display + Clone
    use simple_parser::ast::Type;
    let items = parse("trait Debug: Display + Clone:\n    fn debug(self)");
    if let Node::Trait(t) = &items[0] {
        assert_eq!(t.name, "Debug");
        assert_eq!(t.super_traits.len(), 2);
        assert_eq!(t.super_traits[0], Type::Simple("Display".to_string()));
        assert_eq!(t.super_traits[1], Type::Simple("Clone".to_string()));
    } else {
        panic!("Expected trait");
    }
}

#[test]
fn parse_trait_multiple_generic_inheritance() {
    // Multiple generic trait inheritance: trait IndexedSeq<T>: Seq<T> + Index<usize, T>
    use simple_parser::ast::Type;
    let items = parse("trait IndexedSeq<T>: Seq<T> + Index<usize, T>:\n    fn at(self, i: usize) -> T");
    if let Node::Trait(t) = &items[0] {
        assert_eq!(t.name, "IndexedSeq");
        assert_eq!(t.super_traits.len(), 2);
        // First super trait: Seq<T>
        match &t.super_traits[0] {
            Type::Generic { name, args } => {
                assert_eq!(name, "Seq");
                assert_eq!(args.len(), 1);
            }
            _ => panic!("Expected Seq<T>"),
        }
        // Second super trait: Index<usize, T>
        match &t.super_traits[1] {
            Type::Generic { name, args } => {
                assert_eq!(name, "Index");
                assert_eq!(args.len(), 2);
            }
            _ => panic!("Expected Index<usize, T>"),
        }
    } else {
        panic!("Expected trait");
    }
}
