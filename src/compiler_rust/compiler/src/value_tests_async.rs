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
