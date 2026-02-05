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
