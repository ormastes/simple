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
        assert!(Value::Str("hello".into()).as_int().is_err());
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
        assert_eq!(Value::Str("hello".into()).to_key_string(), "hello");
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
        assert!(Value::Str("hello".into()).truthy());
        assert!(!Value::Str("".into()).truthy());
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
        assert!(Value::Dict(d).truthy());
        assert!(!Value::Dict(HashMap::new()).truthy());
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
        }.truthy());
    }

    #[test]
    fn test_value_truthy_enum() {
        assert!(Value::Enum {
            enum_name: "Option".into(),
            variant: "Some".into(),
            payload: None
        }.truthy());
    }

    // ==========================================================================
    // Value::to_display_string tests
    // ==========================================================================
    #[test]
    fn test_value_to_display_string_str() {
        assert_eq!(Value::Str("hello".into()).to_display_string(), "hello");
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
        assert_eq!(Value::Str("".into()).type_name(), "str");
        assert_eq!(Value::Symbol("".into()).type_name(), "symbol");
        assert_eq!(Value::array(vec![]).type_name(), "array");
        assert_eq!(Value::Tuple(vec![]).type_name(), "tuple");
        assert_eq!(Value::Dict(HashMap::new()).type_name(), "dict");
        assert_eq!(Value::Nil.type_name(), "nil");
        assert_eq!(Value::Object {
            class: "Test".into(),
            fields: Arc::new(HashMap::new())
        }.type_name(), "object");
        assert_eq!(Value::Enum {
            enum_name: "Option".into(),
            variant: "Some".into(),
            payload: None
        }.type_name(), "enum");
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
        assert!(Value::Float(3.15).matches_type("f32"));
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
        assert!(Value::Str("hello".into()).matches_type("str"));
        assert!(Value::Str("hello".into()).matches_type("String"));
        assert!(Value::Str("hello".into()).matches_type("Str"));
        assert!(!Value::Str("hello".into()).matches_type("int"));
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
        assert!(Value::Dict(HashMap::new()).matches_type("dict"));
        assert!(Value::Dict(HashMap::new()).matches_type("Dict"));
    }

    #[test]
    fn test_value_matches_type_object() {
        let obj = Value::Object {
            class: "Person".into(),
            fields: Arc::new(HashMap::new())
        };
        assert!(obj.matches_type("Person"));
        assert!(!obj.matches_type("Car"));
    }

    #[test]
    fn test_value_matches_type_enum() {
        let e = Value::Enum {
            enum_name: "Option".into(),
            variant: "Some".into(),
            payload: None
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
        let v = Value::Str("hello".into());
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
        let v = Value::Dict(d);
        assert_eq!(v.clone(), v);
    }

    #[test]
    fn test_value_clone_object() {
        let v = Value::Object {
            class: "Test".into(),
            fields: Arc::new(HashMap::new())
        };
        assert_eq!(v.clone(), v);
    }

    #[test]
    fn test_value_clone_enum() {
        let v = Value::Enum {
            enum_name: "Option".into(),
            variant: "Some".into(),
            payload: Some(Box::new(Value::Int(42)))
        };
        assert_eq!(v.clone(), v);
    }

    #[test]
    fn test_value_clone_nil() {
        assert_eq!(Value::Nil.clone(), Value::Nil);
    }

    #[test]
    fn test_value_equality_mismatch() {
        assert_ne!(Value::Int(42), Value::Float(42.0));
        assert_ne!(Value::Int(42), Value::Str("42".into()));
        assert_ne!(Value::Bool(true), Value::Int(1));
    }

    // ==========================================================================
