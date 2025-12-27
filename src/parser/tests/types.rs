use simple_parser::ast::{BinaryArithmeticOp, Node, OverflowBehavior, ReferenceCapability, Type, UnaryArithmeticOp, UnitExpr};
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

// Generic types use brackets: List[i64]
#[test]
fn parse_type_alias() {
    parse_ok("type IntList = List[i64]");
}

// === dyn Trait Tests ===

#[test]
fn parse_dyn_trait_type_annotation() {
    // dyn Trait as type annotation in function parameter
    parse_ok("fn process(obj: dyn Display):\n    pass");
}

#[test]
fn parse_dyn_trait_return_type() {
    // dyn Trait as function return type
    parse_ok("fn create() -> dyn Printable:\n    pass");
}

#[test]
fn parse_dyn_trait_in_array() {
    // Array of dyn Trait objects
    parse_ok("let items: [dyn Drawable] = []");
}

#[test]
fn parse_dyn_trait_parses_correctly() {
    let items = parse("fn take(x: dyn Trait):\n    pass");
    if let Node::Function(f) = &items[0] {
        assert_eq!(f.params.len(), 1);
        assert!(matches!(&f.params[0].ty, Some(Type::DynTrait(name)) if name == "Trait"));
    } else {
        panic!("expected function");
    }
}

// === Unit Arithmetic Tests ===

#[test]
fn parse_unit_family_basic() {
    // Basic unit family without arithmetic
    let items = parse("unit length(base: f64): m = 1.0, km = 1000.0");
    if let Node::UnitFamily(uf) = &items[0] {
        assert_eq!(uf.name, "length");
        assert_eq!(uf.variants.len(), 2);
        assert_eq!(uf.variants[0].suffix, "m");
        assert_eq!(uf.variants[0].factor, 1.0);
        assert_eq!(uf.variants[1].suffix, "km");
        assert_eq!(uf.variants[1].factor, 1000.0);
        assert!(uf.arithmetic.is_none());
    } else {
        panic!("expected UnitFamily");
    }
}

#[test]
fn parse_unit_family_with_arithmetic() {
    // Unit family with arithmetic rules
    let code = r#"unit length(base: f64): m = 1.0, km = 1000.0:
    allow add(length) -> length
    allow sub(length) -> length
    allow mul(f64) -> length
    allow neg -> length"#;
    let items = parse(code);
    if let Node::UnitFamily(uf) = &items[0] {
        assert_eq!(uf.name, "length");
        let arith = uf.arithmetic.as_ref().expect("arithmetic");
        assert_eq!(arith.binary_rules.len(), 3);
        assert_eq!(arith.unary_rules.len(), 1);
        // Check binary rules
        assert!(matches!(arith.binary_rules[0].op, BinaryArithmeticOp::Add));
        assert!(matches!(arith.binary_rules[1].op, BinaryArithmeticOp::Sub));
        assert!(matches!(arith.binary_rules[2].op, BinaryArithmeticOp::Mul));
        // Check unary rules
        assert!(matches!(arith.unary_rules[0].op, UnaryArithmeticOp::Neg));
    } else {
        panic!("expected UnitFamily");
    }
}

#[test]
fn parse_unit_family_with_custom_fn() {
    // Unit family with custom function
    let code = r#"unit length(base: f64): m = 1.0:
    allow add(length) -> length
    fn sqrt(self) -> f64:
        return sqrt(self.value())"#;
    let items = parse(code);
    if let Node::UnitFamily(uf) = &items[0] {
        let arith = uf.arithmetic.as_ref().expect("arithmetic");
        assert_eq!(arith.binary_rules.len(), 1);
        assert_eq!(arith.custom_fns.len(), 1);
        assert_eq!(arith.custom_fns[0].name, "sqrt");
    } else {
        panic!("expected UnitFamily");
    }
}

#[test]
fn parse_compound_unit_basic() {
    // Simple compound unit
    let items = parse("unit velocity = length / time");
    if let Node::CompoundUnit(cu) = &items[0] {
        assert_eq!(cu.name, "velocity");
        assert!(matches!(&cu.expr, UnitExpr::Div(_, _)));
        assert!(cu.arithmetic.is_none());
    } else {
        panic!("expected CompoundUnit");
    }
}

#[test]
fn parse_compound_unit_with_power() {
    // Compound unit with exponent
    let items = parse("unit acceleration = length / time^2");
    if let Node::CompoundUnit(cu) = &items[0] {
        assert_eq!(cu.name, "acceleration");
        if let UnitExpr::Div(left, right) = &cu.expr {
            assert!(matches!(left.as_ref(), UnitExpr::Base(n) if n == "length"));
            assert!(matches!(right.as_ref(), UnitExpr::Pow(_, 2)));
        } else {
            panic!("expected Div");
        }
    } else {
        panic!("expected CompoundUnit");
    }
}

#[test]
fn parse_compound_unit_with_arithmetic() {
    // Compound unit with arithmetic rules
    let code = r#"unit velocity = length / time:
    allow add(velocity) -> velocity
    allow mul(time) -> length"#;
    let items = parse(code);
    if let Node::CompoundUnit(cu) = &items[0] {
        assert_eq!(cu.name, "velocity");
        let arith = cu.arithmetic.as_ref().expect("arithmetic");
        assert_eq!(arith.binary_rules.len(), 2);
        // velocity + velocity -> velocity
        assert!(matches!(arith.binary_rules[0].op, BinaryArithmeticOp::Add));
        // velocity * time -> length
        assert!(matches!(arith.binary_rules[1].op, BinaryArithmeticOp::Mul));
    } else {
        panic!("expected CompoundUnit");
    }
}

#[test]
fn parse_compound_unit_multiplication() {
    // Compound unit with multiplication
    let items = parse("unit area = length * length");
    if let Node::CompoundUnit(cu) = &items[0] {
        assert_eq!(cu.name, "area");
        assert!(matches!(&cu.expr, UnitExpr::Mul(_, _)));
    } else {
        panic!("expected CompoundUnit");
    }
}

#[test]
fn parse_compound_unit_complex() {
    // Complex compound unit: force = mass * length / time^2
    let items = parse("unit force = mass * length / time^2");
    if let Node::CompoundUnit(cu) = &items[0] {
        assert_eq!(cu.name, "force");
        // Should parse as (mass * length) / time^2
        if let UnitExpr::Div(left, right) = &cu.expr {
            assert!(matches!(left.as_ref(), UnitExpr::Mul(_, _)));
            assert!(matches!(right.as_ref(), UnitExpr::Pow(_, 2)));
        } else {
            panic!("expected Div");
        }
    } else {
        panic!("expected CompoundUnit");
    }
}

// === Bit-Limited Unit Tests ===

#[test]
fn parse_unit_family_with_repr_block() {
    // Unit family with repr block for allowed representations
    let code = r#"unit length(base: f64): m = 1.0, cm = 0.01:
    repr: u8, u16, u32
    allow add(length) -> length"#;
    let items = parse(code);
    if let Node::UnitFamily(uf) = &items[0] {
        assert_eq!(uf.name, "length");
        let arith = uf.arithmetic.as_ref().expect("arithmetic");
        assert_eq!(arith.allowed_reprs.len(), 3);
        assert!(!arith.allowed_reprs[0].signed); // u8
        assert_eq!(arith.allowed_reprs[0].bits, 8);
        assert!(!arith.allowed_reprs[1].signed); // u16
        assert_eq!(arith.allowed_reprs[1].bits, 16);
        assert!(!arith.allowed_reprs[2].signed); // u32
        assert_eq!(arith.allowed_reprs[2].bits, 32);
    } else {
        panic!("expected UnitFamily");
    }
}

#[test]
fn parse_unit_family_with_repr_mixed() {
    // Unit family with repr block including signed and unsigned types
    let code = r#"unit temperature(base: f64): K = 1.0:
    repr: i8, i16, u12, f32
    allow add(temperature) -> temperature"#;
    let items = parse(code);
    if let Node::UnitFamily(uf) = &items[0] {
        let arith = uf.arithmetic.as_ref().expect("arithmetic");
        assert_eq!(arith.allowed_reprs.len(), 4);
        assert!(arith.allowed_reprs[0].signed); // i8
        assert!(arith.allowed_reprs[1].signed); // i16
        assert!(!arith.allowed_reprs[2].signed); // u12
        assert_eq!(arith.allowed_reprs[2].bits, 12);
        assert!(arith.allowed_reprs[3].is_float); // f32
    } else {
        panic!("expected UnitFamily");
    }
}

#[test]
fn parse_type_unit_with_repr() {
    // Compact syntax: _cm:u12
    let code = "fn measure(x: _cm:u12) -> _cm:u12:\n    return x";
    let items = parse(code);
    if let Node::Function(f) = &items[0] {
        // Check parameter type
        if let Type::UnitWithRepr { name, repr, constraints } = &f.params[0].ty.as_ref().unwrap() {
            assert_eq!(name, "_cm");
            let r = repr.as_ref().expect("repr");
            assert!(!r.signed);
            assert_eq!(r.bits, 12);
            assert!(constraints.range.is_none());
        } else {
            panic!("expected UnitWithRepr for param");
        }
        // Check return type
        if let Type::UnitWithRepr { name, repr, .. } = f.return_type.as_ref().unwrap() {
            assert_eq!(name, "_cm");
            let r = repr.as_ref().expect("repr");
            assert!(!r.signed);
            assert_eq!(r.bits, 12);
        } else {
            panic!("expected UnitWithRepr for return");
        }
    } else {
        panic!("expected function");
    }
}

#[test]
fn parse_type_unit_with_signed_repr() {
    // Compact syntax with signed type: _temp:i16
    let code = "fn read_temp(x: _temp:i16) -> _temp:i32:\n    return x";
    let items = parse(code);
    if let Node::Function(f) = &items[0] {
        if let Type::UnitWithRepr { name, repr, .. } = &f.params[0].ty.as_ref().unwrap() {
            assert_eq!(name, "_temp");
            let r = repr.as_ref().expect("repr");
            assert!(r.signed);
            assert_eq!(r.bits, 16);
        } else {
            panic!("expected UnitWithRepr");
        }
    } else {
        panic!("expected function");
    }
}

#[test]
fn parse_type_unit_with_where_clause() {
    // Where clause syntax: _cm where range: 0..1000
    let code = "fn measure(x: _cm where range: 0..1000) -> _cm:\n    return x";
    let items = parse(code);
    if let Node::Function(f) = &items[0] {
        if let Type::UnitWithRepr { name, repr, constraints } = &f.params[0].ty.as_ref().unwrap() {
            assert_eq!(name, "_cm");
            assert!(repr.is_none()); // No explicit repr
            assert_eq!(constraints.range, Some((0, 1000)));
        } else {
            panic!("expected UnitWithRepr with where clause");
        }
    } else {
        panic!("expected function");
    }
}

#[test]
fn parse_type_unit_with_repr_and_where() {
    // Combined: _cm:u12 where range: 0..4000, checked
    let code = "fn measure(x: _cm:u12 where range: 0..4000, checked) -> _cm:\n    return x";
    let items = parse(code);
    if let Node::Function(f) = &items[0] {
        if let Type::UnitWithRepr { name, repr, constraints } = &f.params[0].ty.as_ref().unwrap() {
            assert_eq!(name, "_cm");
            let r = repr.as_ref().expect("repr");
            assert!(!r.signed);
            assert_eq!(r.bits, 12);
            assert_eq!(constraints.range, Some((0, 4000)));
            assert!(matches!(constraints.overflow, OverflowBehavior::Checked));
        } else {
            panic!("expected UnitWithRepr with repr and where");
        }
    } else {
        panic!("expected function");
    }
}

#[test]
fn parse_type_unit_where_overflow_saturate() {
    // Where clause with saturate overflow
    let code = "fn clamp(x: _percent:u8 where range: 0..100, saturate) -> _percent:\n    return x";
    let items = parse(code);
    if let Node::Function(f) = &items[0] {
        if let Type::UnitWithRepr { constraints, .. } = &f.params[0].ty.as_ref().unwrap() {
            assert_eq!(constraints.range, Some((0, 100)));
            assert!(matches!(constraints.overflow, OverflowBehavior::Saturate));
        } else {
            panic!("expected UnitWithRepr");
        }
    } else {
        panic!("expected function");
    }
}

#[test]
fn parse_type_unit_where_overflow_wrap() {
    // Where clause with wrap overflow
    let code = "fn rotate(x: _angle:u16 where range: 0..360, wrap) -> _angle:\n    return x";
    let items = parse(code);
    if let Node::Function(f) = &items[0] {
        if let Type::UnitWithRepr { constraints, .. } = &f.params[0].ty.as_ref().unwrap() {
            assert_eq!(constraints.range, Some((0, 360)));
            assert!(matches!(constraints.overflow, OverflowBehavior::Wrap));
        } else {
            panic!("expected UnitWithRepr");
        }
    } else {
        panic!("expected function");
    }
}

#[test]
fn parse_type_unit_where_negative_range() {
    // Where clause with negative range
    let code = "fn offset(x: _offset:i16 where range: -500..500) -> _offset:\n    return x";
    let items = parse(code);
    if let Node::Function(f) = &items[0] {
        if let Type::UnitWithRepr { name, repr, constraints } = &f.params[0].ty.as_ref().unwrap() {
            assert_eq!(name, "_offset");
            let r = repr.as_ref().expect("repr");
            assert!(r.signed);
            assert_eq!(r.bits, 16);
            assert_eq!(constraints.range, Some((-500, 500)));
        } else {
            panic!("expected UnitWithRepr");
        }
    } else {
        panic!("expected function");
    }
}

// Capability tests
#[test]
fn test_capability_mut_type() {
    // Parse mut T syntax
    let code = "fn update(x: mut Counter) -> i64:\n    return 0";
    let items = parse(code);
    if let Node::Function(f) = &items[0] {
        if let Type::Capability { capability, inner } = &f.params[0].ty.as_ref().unwrap() {
            assert_eq!(*capability, ReferenceCapability::Exclusive);
            assert!(matches!(&**inner, Type::Simple(name) if name == "Counter"));
        } else {
            panic!("expected Capability type, got {:?}", f.params[0].ty);
        }
    } else {
        panic!("expected function");
    }
}

#[test]
fn test_capability_iso_type() {
    // Parse iso T syntax
    let code = "fn transfer(data: iso Data) -> i64:\n    return 0";
    let items = parse(code);
    if let Node::Function(f) = &items[0] {
        if let Type::Capability { capability, inner } = &f.params[0].ty.as_ref().unwrap() {
            assert_eq!(*capability, ReferenceCapability::Isolated);
            assert!(matches!(&**inner, Type::Simple(name) if name == "Data"));
        } else {
            panic!("expected Capability type, got {:?}", f.params[0].ty);
        }
    } else {
        panic!("expected function");
    }
}

#[test]
fn test_capability_default_shared() {
    // No prefix = default (Shared) capability
    let code = "fn read(x: Counter) -> i64:\n    return 0";
    let items = parse(code);
    if let Node::Function(f) = &items[0] {
        // Default capability should just be a Simple type (no Capability wrapper)
        assert!(matches!(&f.params[0].ty, Some(Type::Simple(name)) if name == "Counter"));
    } else {
        panic!("expected function");
    }
}

#[test]
fn test_capability_with_generic() {
    // mut with generic type
    let code = "fn modify(x: mut List[i64]) -> i64:\n    return 0";
    let items = parse(code);
    if let Node::Function(f) = &items[0] {
        if let Type::Capability { capability, inner } = &f.params[0].ty.as_ref().unwrap() {
            assert_eq!(*capability, ReferenceCapability::Exclusive);
            assert!(matches!(&**inner, Type::Generic { name, .. } if name == "List"));
        } else {
            panic!("expected Capability type");
        }
    } else {
        panic!("expected function");
    }
}

#[test]
fn test_capability_nested() {
    // Nested capability types (should parse but semantically invalid)
    let code = "fn weird(x: mut mut Counter) -> i64:\n    return 0";
    let items = parse(code);
    if let Node::Function(f) = &items[0] {
        // Should parse as Capability(Exclusive, Capability(Exclusive, Counter))
        if let Type::Capability { capability: cap1, inner: inner1 } = &f.params[0].ty.as_ref().unwrap() {
            assert_eq!(*cap1, ReferenceCapability::Exclusive);
            if let Type::Capability { capability: cap2, .. } = &**inner1 {
                assert_eq!(*cap2, ReferenceCapability::Exclusive);
            } else {
                panic!("expected nested Capability");
            }
        } else {
            panic!("expected Capability type");
        }
    } else {
        panic!("expected function");
    }
}
