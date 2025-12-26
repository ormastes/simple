// Tests for value.rs - included via include!() macro

#[cfg(test)]
mod tests {
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
        assert_eq!(Value::Float(3.14).as_float().unwrap(), 3.14);
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
        assert_eq!(Value::Float(3.14).to_key_string(), "3.14");
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
        assert!(Value::Array(vec![Value::Int(1)]).truthy());
        assert!(!Value::Array(vec![]).truthy());
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
            fields: HashMap::new()
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
        assert_eq!(Value::Float(3.14).to_display_string(), "3.14");
    }

    #[test]
    fn test_value_to_display_string_bool() {
        assert_eq!(Value::Bool(true).to_display_string(), "true");
        assert_eq!(Value::Bool(false).to_display_string(), "false");
    }

    #[test]
    fn test_value_to_display_string_array() {
        let arr = Value::Array(vec![Value::Int(1), Value::Int(2)]);
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
        assert_eq!(Value::Array(vec![]).type_name(), "array");
        assert_eq!(Value::Tuple(vec![]).type_name(), "tuple");
        assert_eq!(Value::Dict(HashMap::new()).type_name(), "dict");
        assert_eq!(Value::Nil.type_name(), "nil");
        assert_eq!(Value::Object {
            class: "Test".into(),
            fields: HashMap::new()
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
        assert!(Value::Float(3.14).matches_type("f64"));
        assert!(Value::Float(3.14).matches_type("f32"));
        assert!(Value::Float(3.14).matches_type("float"));
        assert!(Value::Float(3.14).matches_type("Float"));
        assert!(!Value::Float(3.14).matches_type("int"));
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
        assert!(Value::Array(vec![]).matches_type("array"));
        assert!(Value::Array(vec![]).matches_type("Array"));
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
            fields: HashMap::new()
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
        let v = Value::Float(3.14);
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
        let v = Value::Array(vec![Value::Int(1), Value::Int(2)]);
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
            fields: HashMap::new()
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
    // GeneratorValue tests
    // ==========================================================================
    #[test]
    fn test_generator_new_with_values() {
        let gen = GeneratorValue::new_with_values(vec![Value::Int(1), Value::Int(2), Value::Int(3)]);
        assert!(!gen.is_done());
    }

    #[test]
    fn test_generator_next() {
        let gen = GeneratorValue::new_with_values(vec![Value::Int(1), Value::Int(2)]);
        assert_eq!(gen.next(), Some(Value::Int(1)));
        assert_eq!(gen.next(), Some(Value::Int(2)));
        assert_eq!(gen.next(), None);
        assert!(gen.is_done());
    }

    #[test]
    fn test_generator_collect_remaining() {
        let gen = GeneratorValue::new_with_values(vec![Value::Int(1), Value::Int(2), Value::Int(3)]);
        let _ = gen.next(); // consume first
        let remaining = gen.collect_remaining();
        assert_eq!(remaining.len(), 2);
    }

    #[test]
    fn test_generator_clone() {
        let gen = GeneratorValue::new_with_values(vec![Value::Int(1), Value::Int(2)]);
        let gen2 = gen.clone();
        // Clones share state
        assert_eq!(gen.next(), Some(Value::Int(1)));
        assert_eq!(gen2.next(), Some(Value::Int(2))); // continues from where gen left off
    }

    #[test]
    fn test_generator_equality() {
        let gen = GeneratorValue::new_with_values(vec![Value::Int(1)]);
        let gen2 = gen.clone();
        assert_eq!(gen, gen2); // Same Arc pointers
    }

    // ==========================================================================
    // GeneratorState tests
    // ==========================================================================
    #[test]
    fn test_generator_state_equality() {
        assert_eq!(GeneratorState::Created, GeneratorState::Created);
        assert_eq!(GeneratorState::Suspended, GeneratorState::Suspended);
        assert_eq!(GeneratorState::Completed, GeneratorState::Completed);
        assert_ne!(GeneratorState::Created, GeneratorState::Completed);
    }

    // ==========================================================================
    // FutureValue tests
    // ==========================================================================
    #[test]
    fn test_future_value_new_and_await() {
        let future = FutureValue::new(|| Ok(Value::Int(42)));
        let result = future.await_result();
        assert_eq!(result.unwrap(), Value::Int(42));
    }

    #[test]
    fn test_future_value_is_ready() {
        let future = FutureValue::new(|| Ok(Value::Int(42)));
        // Give thread time to complete
        std::thread::sleep(std::time::Duration::from_millis(10));
        assert!(future.is_ready());
    }

    #[test]
    fn test_future_value_clone() {
        let future = FutureValue::new(|| Ok(Value::Int(42)));
        let future2 = future.clone();
        // Clones share the same Arc pointers
        assert!(Arc::ptr_eq(&future.result, &future2.result));
    }

    #[test]
    fn test_future_value_equality() {
        let future = FutureValue::new(|| Ok(Value::Int(42)));
        let future2 = future.clone();
        assert_eq!(future, future2);
    }

    // ==========================================================================
    // ManualUniqueValue tests
    // ==========================================================================
    #[test]
    fn test_manual_unique_value_new() {
        let u = ManualUniqueValue::new(Value::Int(42));
        assert_eq!(u.inner(), &Value::Int(42));
    }

    #[test]
    fn test_manual_unique_value_into_inner() {
        let u = ManualUniqueValue::new(Value::Int(42));
        assert_eq!(u.into_inner(), Value::Int(42));
    }

    #[test]
    fn test_manual_unique_value_clone() {
        let u = ManualUniqueValue::new(Value::Int(42));
        let u2 = u.clone();
        assert_eq!(u.inner(), u2.inner());
    }

    #[test]
    fn test_manual_unique_value_equality() {
        let u1 = ManualUniqueValue::new(Value::Int(42));
        let u2 = ManualUniqueValue::new(Value::Int(42));
        assert_eq!(u1, u2);
    }

    // ==========================================================================
    // ManualSharedValue tests
    // ==========================================================================
    #[test]
    fn test_manual_shared_value_new() {
        let s = ManualSharedValue::new(Value::Int(42));
        assert_eq!(s.inner(), &Value::Int(42));
    }

    #[test]
    fn test_manual_shared_value_into_inner() {
        let s = ManualSharedValue::new(Value::Int(42));
        assert_eq!(s.into_inner(), Value::Int(42));
    }

    #[test]
    fn test_manual_shared_value_clone() {
        let s = ManualSharedValue::new(Value::Int(42));
        let s2 = s.clone();
        assert_eq!(s.inner(), s2.inner());
    }

    #[test]
    fn test_manual_shared_value_equality() {
        let s1 = ManualSharedValue::new(Value::Int(42));
        let s2 = ManualSharedValue::new(Value::Int(42));
        assert_eq!(s1, s2);
    }

    // ==========================================================================
    // ManualWeakValue tests
    // ==========================================================================
    #[test]
    fn test_manual_weak_value_new_from_shared() {
        let s = ManualSharedValue::new(Value::Int(42));
        let w = ManualWeakValue::new_from_shared(&s);
        assert_eq!(w.upgrade_inner(), Some(Value::Int(42)));
    }

    #[test]
    fn test_manual_weak_value_clone() {
        let s = ManualSharedValue::new(Value::Int(42));
        let w = ManualWeakValue::new_from_shared(&s);
        let w2 = w.clone();
        assert_eq!(w.upgrade_inner(), w2.upgrade_inner());
    }

    #[test]
    fn test_manual_weak_value_equality() {
        let s = ManualSharedValue::new(Value::Int(42));
        let w1 = ManualWeakValue::new_from_shared(&s);
        let w2 = ManualWeakValue::new_from_shared(&s);
        assert_eq!(w1.upgrade_inner(), w2.upgrade_inner());
    }

    // ==========================================================================
    // ManualHandleValue tests
    // ==========================================================================
    #[test]
    fn test_manual_handle_value_new() {
        let h = ManualHandleValue::new(Value::Int(42));
        assert_eq!(h.resolve_inner(), Some(Value::Int(42)));
    }

    #[test]
    fn test_manual_handle_value_clone() {
        let h = ManualHandleValue::new(Value::Int(42));
        let h2 = h.clone();
        assert_eq!(h.resolve_inner(), h2.resolve_inner());
    }

    #[test]
    fn test_manual_handle_value_equality() {
        let h1 = ManualHandleValue::new(Value::Int(42));
        let h2 = ManualHandleValue::new(Value::Int(42));
        assert_eq!(h1.resolve_inner(), h2.resolve_inner());
    }

    // ==========================================================================
    // BorrowValue tests
    // ==========================================================================
    #[test]
    fn test_borrow_value_new() {
        let b = BorrowValue::new(Value::Int(42));
        assert_eq!(*b.inner(), Value::Int(42));
    }

    #[test]
    fn test_borrow_value_from_arc() {
        let arc = Arc::new(RwLock::new(Value::Int(42)));
        let b = BorrowValue::from_arc(arc);
        assert_eq!(*b.inner(), Value::Int(42));
    }

    #[test]
    fn test_borrow_value_get_arc() {
        let b = BorrowValue::new(Value::Int(42));
        let arc = b.get_arc();
        assert_eq!(*arc.read().unwrap(), Value::Int(42));
    }

    #[test]
    fn test_borrow_value_clone() {
        let b = BorrowValue::new(Value::Int(42));
        let b2 = b.clone();
        // Clones share the same Arc
        assert!(Arc::ptr_eq(&b.get_arc(), &b2.get_arc()));
    }

    #[test]
    fn test_borrow_value_equality() {
        let b1 = BorrowValue::new(Value::Int(42));
        let b2 = BorrowValue::new(Value::Int(42));
        assert_eq!(b1, b2);
    }

    // ==========================================================================
    // BorrowMutValue tests
    // ==========================================================================
    #[test]
    fn test_borrow_mut_value_new() {
        let b = BorrowMutValue::new(Value::Int(42));
        assert_eq!(*b.inner(), Value::Int(42));
    }

    #[test]
    fn test_borrow_mut_value_inner_mut() {
        let b = BorrowMutValue::new(Value::Int(42));
        *b.inner_mut() = Value::Int(100);
        assert_eq!(*b.inner(), Value::Int(100));
    }

    #[test]
    fn test_borrow_mut_value_from_arc() {
        let arc = Arc::new(RwLock::new(Value::Int(42)));
        let b = BorrowMutValue::from_arc(arc);
        assert_eq!(*b.inner(), Value::Int(42));
    }

    #[test]
    fn test_borrow_mut_value_clone() {
        let b = BorrowMutValue::new(Value::Int(42));
        let b2 = b.clone();
        // Clones share the same Arc
        assert!(Arc::ptr_eq(&b.get_arc(), &b2.get_arc()));
    }

    #[test]
    fn test_borrow_mut_value_equality() {
        let b1 = BorrowMutValue::new(Value::Int(42));
        let b2 = BorrowMutValue::new(Value::Int(42));
        assert_eq!(b1, b2);
    }

    // ==========================================================================
    // Pointer-wrapped value tests
    // ==========================================================================
    #[test]
    fn test_value_unique_as_int() {
        let u = ManualUniqueValue::new(Value::Int(42));
        assert_eq!(Value::Unique(u).as_int().unwrap(), 42);
    }

    #[test]
    fn test_value_shared_as_int() {
        let s = ManualSharedValue::new(Value::Int(42));
        assert_eq!(Value::Shared(s).as_int().unwrap(), 42);
    }

    #[test]
    fn test_value_borrow_as_int() {
        let b = BorrowValue::new(Value::Int(42));
        assert_eq!(Value::Borrow(b).as_int().unwrap(), 42);
    }

    #[test]
    fn test_value_borrow_mut_as_int() {
        let b = BorrowMutValue::new(Value::Int(42));
        assert_eq!(Value::BorrowMut(b).as_int().unwrap(), 42);
    }

    #[test]
    fn test_value_unique_truthy() {
        let u = ManualUniqueValue::new(Value::Int(42));
        assert!(Value::Unique(u).truthy());
    }

    #[test]
    fn test_value_shared_truthy() {
        let s = ManualSharedValue::new(Value::Int(42));
        assert!(Value::Shared(s).truthy());
    }

    #[test]
    fn test_value_borrow_truthy() {
        let b = BorrowValue::new(Value::Int(42));
        assert!(Value::Borrow(b).truthy());
    }

    #[test]
    fn test_value_borrow_mut_truthy() {
        let b = BorrowMutValue::new(Value::Int(42));
        assert!(Value::BorrowMut(b).truthy());
    }

    #[test]
    fn test_value_unique_to_key_string() {
        let u = ManualUniqueValue::new(Value::Int(42));
        assert_eq!(Value::Unique(u).to_key_string(), "42");
    }

    #[test]
    fn test_value_shared_to_key_string() {
        let s = ManualSharedValue::new(Value::Int(42));
        assert_eq!(Value::Shared(s).to_key_string(), "42");
    }

    #[test]
    fn test_value_unique_to_display_string() {
        let u = ManualUniqueValue::new(Value::Int(42));
        assert_eq!(Value::Unique(u).to_display_string(), "&42");
    }

    #[test]
    fn test_value_shared_to_display_string() {
        let s = ManualSharedValue::new(Value::Int(42));
        assert_eq!(Value::Shared(s).to_display_string(), "*42");
    }

    #[test]
    fn test_value_borrow_to_display_string() {
        let b = BorrowValue::new(Value::Int(42));
        assert_eq!(Value::Borrow(b).to_display_string(), "&42");
    }

    #[test]
    fn test_value_borrow_mut_to_display_string() {
        let b = BorrowMutValue::new(Value::Int(42));
        assert_eq!(Value::BorrowMut(b).to_display_string(), "&mut 42");
    }

    // ==========================================================================
    // Pointer deref tests
    // ==========================================================================
    #[test]
    fn test_value_deref_unique() {
        let u = ManualUniqueValue::new(Value::Int(42));
        assert_eq!(Value::Unique(u).deref_pointer(), Value::Int(42));
    }

    #[test]
    fn test_value_deref_shared() {
        let s = ManualSharedValue::new(Value::Int(42));
        assert_eq!(Value::Shared(s).deref_pointer(), Value::Int(42));
    }

    #[test]
    fn test_value_deref_borrow() {
        let b = BorrowValue::new(Value::Int(42));
        assert_eq!(Value::Borrow(b).deref_pointer(), Value::Int(42));
    }

    #[test]
    fn test_value_deref_borrow_mut() {
        let b = BorrowMutValue::new(Value::Int(42));
        assert_eq!(Value::BorrowMut(b).deref_pointer(), Value::Int(42));
    }

    // ==========================================================================
    // Magic constants tests
    // ==========================================================================
    #[test]
    fn test_builtin_range_constant() {
        assert_eq!(BUILTIN_RANGE, "__range__");
    }

    #[test]
    fn test_builtin_array_constant() {
        assert_eq!(BUILTIN_ARRAY, "__array__");
    }
}
