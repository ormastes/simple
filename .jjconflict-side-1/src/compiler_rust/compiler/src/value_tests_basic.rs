use super::*;

// ==========================================================================
// ClassName tests
// ==========================================================================
#[test]
fn test_class_name_new() {
    let cn = ClassName::new("MyClass");
    assert_eq!(cn.as_str(), "MyClass");
}

#[test]
fn test_class_name_from_str() {
    let cn: ClassName = "MyClass".into();
    assert_eq!(cn.as_str(), "MyClass");
}

#[test]
fn test_class_name_from_string() {
    let cn: ClassName = String::from("MyClass").into();
    assert_eq!(cn.as_str(), "MyClass");
}

// ==========================================================================
// EnumTypeName tests
// ==========================================================================
#[test]
fn test_enum_type_name_new() {
    let en = EnumTypeName::new("Option");
    assert_eq!(en.as_str(), "Option");
}

#[test]
fn test_enum_type_name_from_str() {
    let en: EnumTypeName = "Result".into();
    assert_eq!(en.as_str(), "Result");
}

#[test]
fn test_enum_type_name_from_string() {
    let en: EnumTypeName = String::from("Either").into();
    assert_eq!(en.as_str(), "Either");
}

// ==========================================================================
// VariantName tests
// ==========================================================================
#[test]
fn test_variant_name_new() {
    let vn = VariantName::new("Some");
    assert_eq!(vn.as_str(), "Some");
}

#[test]
fn test_variant_name_from_str() {
    let vn: VariantName = "None".into();
    assert_eq!(vn.as_str(), "None");
}

#[test]
fn test_variant_name_from_string() {
    let vn: VariantName = String::from("Ok").into();
    assert_eq!(vn.as_str(), "Ok");
}

// ==========================================================================
// Value::as_int tests
// ==========================================================================
#[test]
fn test_value_as_int_from_int() {
    assert_eq!(Value::Int(42).as_int().unwrap(), 42);
}

#[test]
fn test_value_as_int_from_float() {
    assert_eq!(Value::Float(3.7).as_int().unwrap(), 3);
}

#[test]
fn test_value_as_int_from_bool() {
    assert_eq!(Value::Bool(true).as_int().unwrap(), 1);
    assert_eq!(Value::Bool(false).as_int().unwrap(), 0);
}

#[test]
fn test_value_as_int_from_nil() {
    assert_eq!(Value::Nil.as_int().unwrap(), 0);
}

#[test]
fn test_value_as_int_from_string_fails() {
    assert!(Value::text("hello").as_int().is_err());
}

#[test]
fn test_value_as_int_from_symbol_fails() {
    assert!(Value::Symbol("sym".into()).as_int().is_err());
}

// ==========================================================================
// Value::as_float tests
// ==========================================================================
#[test]
fn test_value_as_float_from_float() {
    assert_eq!(Value::Float(3.15).as_float().unwrap(), 3.15);
}

#[test]
fn test_value_as_float_from_int() {
    assert_eq!(Value::Int(42).as_float().unwrap(), 42.0);
}

#[test]
fn test_value_as_float_from_bool() {
    assert_eq!(Value::Bool(true).as_float().unwrap(), 1.0);
    assert_eq!(Value::Bool(false).as_float().unwrap(), 0.0);
}

#[test]
fn test_value_as_float_from_nil() {
    assert_eq!(Value::Nil.as_float().unwrap(), 0.0);
}

// ==========================================================================
// Value::to_key_string tests
// ==========================================================================
#[test]
fn test_value_to_key_string_int() {
    assert_eq!(Value::Int(42).to_key_string(), "42");
}

#[test]
fn test_value_to_key_string_float() {
    assert_eq!(Value::Float(3.15).to_key_string(), "3.15");
}

#[test]
fn test_value_to_key_string_bool() {
    assert_eq!(Value::Bool(true).to_key_string(), "true");
    assert_eq!(Value::Bool(false).to_key_string(), "false");
}

#[test]
fn test_value_to_key_string_str() {
    assert_eq!(Value::text("hello").to_key_string(), "hello");
}

#[test]
fn test_value_to_key_string_symbol() {
    assert_eq!(Value::Symbol("sym".into()).to_key_string(), "sym");
}

#[test]
fn test_value_to_key_string_nil() {
    assert_eq!(Value::Nil.to_key_string(), "nil");
}

// ==========================================================================
// Value::truthy tests
// ==========================================================================
#[test]
fn test_value_truthy_bool() {
    assert!(Value::Bool(true).truthy());
    assert!(!Value::Bool(false).truthy());
}

#[test]
fn test_value_truthy_int() {
    assert!(Value::Int(1).truthy());
    assert!(Value::Int(-1).truthy());
    assert!(!Value::Int(0).truthy());
}

#[test]
fn test_value_truthy_float() {
    assert!(Value::Float(1.0).truthy());
    assert!(Value::Float(-1.0).truthy());
    assert!(!Value::Float(0.0).truthy());
}

#[test]
fn test_value_truthy_str() {
    assert!(Value::text("hello").truthy());
    assert!(!Value::text("").truthy());
}

#[test]
fn test_value_truthy_symbol() {
    assert!(Value::Symbol("sym".into()).truthy());
}

#[test]
fn test_value_truthy_array() {
    assert!(Value::array(vec![Value::Int(1)]).truthy());
    assert!(!Value::array(vec![]).truthy());
}

#[test]
fn test_value_truthy_tuple() {
    assert!(Value::Tuple(vec![Value::Int(1)]).truthy());
    assert!(!Value::Tuple(vec![]).truthy());
}

#[test]
fn test_value_truthy_dict() {
    let mut d = HashMap::new();
    d.insert("key".to_string(), Value::Int(1));
    assert!(Value::Dict(d.into()).truthy());
    assert!(!Value::Dict(HashMap::new().into()).truthy());
}

#[test]
fn test_value_truthy_nil() {
    assert!(!Value::Nil.truthy());
}

#[test]
fn test_value_truthy_object() {
    assert!(Value::Object {
        class: "Test".into(),
        fields: Arc::new(HashMap::new())
    }
    .truthy());
}

#[test]
fn test_value_truthy_enum() {
    assert!(Value::Enum {
        enum_name: "Option".into(),
        variant: "Some".into(),
        payload: None
    }
    .truthy());
}

// ==========================================================================
// Value::to_display_string tests
// ==========================================================================
#[test]
fn test_value_to_display_string_str() {
    assert_eq!(Value::text("hello").to_display_string(), "hello");
}

#[test]
fn test_value_to_display_string_symbol() {
    assert_eq!(Value::Symbol("sym".into()).to_display_string(), ":sym");
}

#[test]
fn test_value_to_display_string_int() {
    assert_eq!(Value::Int(42).to_display_string(), "42");
}

#[test]
fn test_value_to_display_string_float() {
    assert_eq!(Value::Float(3.15).to_display_string(), "3.15");
}

#[test]
fn test_value_to_display_string_bool() {
    assert_eq!(Value::Bool(true).to_display_string(), "true");
    assert_eq!(Value::Bool(false).to_display_string(), "false");
}

#[test]
fn test_value_to_display_string_array() {
    let arr = Value::array(vec![Value::Int(1), Value::Int(2)]);
    assert_eq!(arr.to_display_string(), "[1, 2]");
}

#[test]
fn test_value_to_display_string_tuple() {
    let tup = Value::Tuple(vec![Value::Int(1), Value::Int(2)]);
    assert_eq!(tup.to_display_string(), "(1, 2)");
}

#[test]
fn test_value_to_display_string_nil() {
    assert_eq!(Value::Nil.to_display_string(), "nil");
}

// ==========================================================================
// Value::type_name tests
// ==========================================================================
#[test]
fn test_value_type_name() {
    assert_eq!(Value::Int(0).type_name(), "i64");
    assert_eq!(Value::Float(0.0).type_name(), "f64");
    assert_eq!(Value::Bool(true).type_name(), "bool");
    assert_eq!(Value::text("").type_name(), "str");
    assert_eq!(Value::Symbol("".into()).type_name(), "symbol");
    assert_eq!(Value::array(vec![]).type_name(), "array");
    assert_eq!(Value::Tuple(vec![]).type_name(), "tuple");
    assert_eq!(Value::Dict(HashMap::new().into()).type_name(), "dict");
    assert_eq!(Value::Nil.type_name(), "nil");
    assert_eq!(
        Value::Object {
            class: "Test".into(),
            fields: Arc::new(HashMap::new())
        }
        .type_name(),
        "object"
    );
    assert_eq!(
        Value::Enum {
            enum_name: "Option".into(),
            variant: "Some".into(),
            payload: None
        }
        .type_name(),
        "enum"
    );
}

// ==========================================================================
// Value::matches_type tests
// ==========================================================================
#[test]
fn test_value_matches_type_int() {
    assert!(Value::Int(42).matches_type("i64"));
    assert!(Value::Int(42).matches_type("i32"));
    assert!(Value::Int(42).matches_type("int"));
    assert!(Value::Int(42).matches_type("Int"));
    assert!(!Value::Int(42).matches_type("str"));
}

#[test]
fn test_value_matches_type_float() {
    assert!(Value::Float(3.15).matches_type("f64"));
    // `matches_type` exists for union-arm discrimination, so it separates the
    // two float representations: "f32" matches `Value::Float32`, not
    // `Value::Float`. The single-precision arm was introduced with the
    // `Value::Float32` variant; "float"/"Float" still matches either.
    assert!(!Value::Float(3.15).matches_type("f32"));
    assert!(Value::Float32(3.15).matches_type("f32"));
    assert!(!Value::Float32(3.15).matches_type("f64"));
    assert!(Value::Float32(3.15).matches_type("float"));
    assert!(Value::Float(3.15).matches_type("float"));
    assert!(Value::Float(3.15).matches_type("Float"));
    assert!(!Value::Float(3.15).matches_type("int"));
}

#[test]
fn test_value_matches_type_bool() {
    assert!(Value::Bool(true).matches_type("bool"));
    assert!(Value::Bool(true).matches_type("Bool"));
    assert!(!Value::Bool(true).matches_type("int"));
}

#[test]
fn test_value_matches_type_str() {
    assert!(Value::text("hello").matches_type("str"));
    assert!(Value::text("hello").matches_type("String"));
    assert!(Value::text("hello").matches_type("Str"));
    assert!(!Value::text("hello").matches_type("int"));
}

#[test]
fn test_value_matches_type_nil() {
    assert!(Value::Nil.matches_type("nil"));
    assert!(Value::Nil.matches_type("Nil"));
    assert!(Value::Nil.matches_type("None"));
    assert!(!Value::Nil.matches_type("int"));
}

#[test]
fn test_value_matches_type_array() {
    assert!(Value::array(vec![]).matches_type("array"));
    assert!(Value::array(vec![]).matches_type("Array"));
}

#[test]
fn test_value_matches_type_tuple() {
    assert!(Value::Tuple(vec![]).matches_type("tuple"));
    assert!(Value::Tuple(vec![]).matches_type("Tuple"));
}

#[test]
fn test_value_matches_type_dict() {
    assert!(Value::Dict(HashMap::new().into()).matches_type("dict"));
    assert!(Value::Dict(HashMap::new().into()).matches_type("Dict"));
}

#[test]
fn test_value_matches_type_object() {
    let obj = Value::Object {
        class: "Person".into(),
        fields: Arc::new(HashMap::new()),
    };
    assert!(obj.matches_type("Person"));
    assert!(!obj.matches_type("Car"));
}

#[test]
fn test_value_matches_type_enum() {
    let e = Value::Enum {
        enum_name: "Option".into(),
        variant: "Some".into(),
        payload: None,
    };
    assert!(e.matches_type("Option"));
    assert!(!e.matches_type("Result"));
}

// ==========================================================================
// Value::deref_pointer tests
// ==========================================================================
#[test]
fn test_value_deref_pointer_non_pointer() {
    let v = Value::Int(42).deref_pointer();
    assert_eq!(v, Value::Int(42));
}

// ==========================================================================
// Value clone and equality tests
// ==========================================================================
#[test]
fn test_value_clone_int() {
    let v = Value::Int(42);
    assert_eq!(v.clone(), v);
}

#[test]
fn test_value_clone_float() {
    let v = Value::Float(3.15);
    assert_eq!(v.clone(), v);
}

#[test]
fn test_value_clone_bool() {
    let v = Value::Bool(true);
    assert_eq!(v.clone(), v);
}

#[test]
fn test_value_clone_str() {
    let v = Value::text("hello");
    assert_eq!(v.clone(), v);
}

#[test]
fn test_value_clone_symbol() {
    let v = Value::Symbol("sym".into());
    assert_eq!(v.clone(), v);
}

#[test]
fn test_value_clone_array() {
    let v = Value::array(vec![Value::Int(1), Value::Int(2)]);
    assert_eq!(v.clone(), v);
}

#[test]
fn test_value_clone_tuple() {
    let v = Value::Tuple(vec![Value::Int(1), Value::Int(2)]);
    assert_eq!(v.clone(), v);
}

#[test]
fn test_value_clone_dict() {
    let mut d = HashMap::new();
    d.insert("key".to_string(), Value::Int(42));
    let v = Value::Dict(d.into());
    assert_eq!(v.clone(), v);
}

#[test]
fn test_value_clone_object() {
    let v = Value::Object {
        class: "Test".into(),
        fields: Arc::new(HashMap::new()),
    };
    assert_eq!(v.clone(), v);
}

#[test]
fn test_value_clone_enum() {
    let v = Value::Enum {
        enum_name: "Option".into(),
        variant: "Some".into(),
        payload: Some(Box::new(Value::Int(42))),
    };
    assert_eq!(v.clone(), v);
}

#[test]
fn test_value_clone_nil() {
    assert_eq!(Value::Nil.clone(), Value::Nil);
}

#[test]
fn shared_text_clone_preserves_buffer_identity() {
    let original = Value::text("shared source".to_string());
    let cloned = original.clone();
    let (Value::Str(original), Value::Str(cloned)) = (&original, &cloned) else {
        panic!("expected text values");
    };
    assert!(Arc::ptr_eq(original, cloned));
    assert_eq!(original.as_ptr(), cloned.as_ptr());
}

#[test]
fn alias_concat_isolation() {
    let source = r#"
var original = "abc"
var changed = original
changed = changed + "def"
main = if original == "abc" and changed == "abcdef": 1 else: 0
"#;
    let module = simple_parser::Parser::new(source).parse().expect("parse alias concat");
    let result = crate::interpreter::evaluate_module(&module.items).expect("evaluate alias concat");
    assert_eq!(result, 1);
}

#[test]
fn shared_text_unicode_index_and_slice() {
    // Bracket SLICES are BYTE-indexed (matching the native lane's rt_slice
    // and the byte-indexed .slice()/.substring() methods): "aé🙂z" is bytes
    // a=0, é=1-2, 🙂=3-6, z=7, so value[1:3] is the two bytes of é. The
    // previous expectation ("é🙂") pinned the interpreter's char-indexed
    // slicing — the engine divergence behind
    // doc/08_tracking/bug/test_harness_execution_divergence_2026-07-29.md.
    // Single-character INDEXING (value[1], value[-2]) keeps character
    // semantics, like char_at/char_code_at.
    let source = r#"
var value = "aé🙂z"
main = if value[1] == "é" and value[-2] == "🙂" and value[1:3] == "é" and value[3:7] == "🙂": 1 else: 0
"#;
    let module = simple_parser::Parser::new(source).parse().expect("parse Unicode text operations");
    let result = crate::interpreter::evaluate_module(&module.items).expect("evaluate Unicode text operations");
    assert_eq!(result, 1);
}

#[test]
fn shared_text_content_key_display_and_ordering() {
    let left = Value::text("alpha".to_string());
    let equal = Value::text("alpha".to_string());
    assert_eq!(left, equal);
    assert_eq!(left.to_key_string(), "alpha");
    assert_eq!(left.to_display_string(), "alpha");

    let source = r#"main = if "alpha" < "beta" and "beta" > "alpha": 1 else: 0"#;
    let module = simple_parser::Parser::new(source).parse().expect("parse text ordering");
    assert_eq!(crate::interpreter::evaluate_module(&module.items).expect("evaluate text ordering"), 1);
}

#[test]
fn shared_text_transform_alias_isolation() {
    let source = r#"
var original = " Abc "
var upper = original.to_upper()
var replaced = original.replace("b", "x")
var sliced = original[1:4]
main = if original == " Abc " and upper == " ABC " and replaced == " Axc " and sliced == "Abc": 1 else: 0
"#;
    let module = simple_parser::Parser::new(source).parse().expect("parse text transforms");
    assert_eq!(crate::interpreter::evaluate_module(&module.items).expect("evaluate text transforms"), 1);
}

#[test]
fn test_value_equality_mismatch() {
    assert_ne!(Value::Int(42), Value::Float(42.0));
    assert_ne!(Value::Int(42), Value::text("42"));
    assert_ne!(Value::Bool(true), Value::Int(1));
}

// ==========================================================================

    // FrameMap (ahash) swap + `insert` empty-set guards, 2026-08-22: the
    // per-frame maps changed hasher and `insert` skips the tombstone /
    // refreshed-global removes when those sets are empty. Every observable
    // behaviour must be byte-identical: `from_map` round-trips through
    // `to_map`, a removed shared key stays hidden behind its tombstone, and a
    // re-insert clears that tombstone again.
    #[test]
    fn cow_env_frame_maps_round_trip_and_tombstone_clear() {
        let mut seed = HashMap::new();
        seed.insert("a".to_string(), Value::Int(1));
        seed.insert("b".to_string(), Value::Int(2));
        let env = CowEnv::from_map(seed.clone());
        assert_eq!(env.to_map().len(), 2);
        assert_eq!(env.get("a"), Some(&Value::Int(1)));

        let base = Arc::new(seed);
        let mut layered = CowEnv::with_base(base);
        assert_eq!(layered.get("b"), Some(&Value::Int(2)));
        // remove a shared key -> tombstone hides it
        assert_eq!(layered.remove("b"), Some(Value::Int(2)));
        assert!(!layered.contains_key("b"));
        assert_eq!(layered.get("b"), None);
        // insert must clear the tombstone (the guarded remove path)
        layered.insert("b".to_string(), Value::Int(3));
        assert!(layered.contains_key("b"));
        assert_eq!(layered.get("b"), Some(&Value::Int(3)));
        assert_eq!(layered.to_map().get("b"), Some(&Value::Int(3)));
    }
