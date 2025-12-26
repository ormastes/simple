//! Example: Integrating fluent API with mockall
//!
//! This example shows how to use the fluent API alongside mockall
//! for setting up and verifying mocks in tests.

// This is an example file, main function just for compilation
fn main() {
    println!("Run with: cargo test -p simple_mock_helper --example fluent_integration");
}

#[cfg(test)]
mod tests {
    use simple_mock_helper::fluent::{MockSetup, MockVerify, Spy};
    
    // Simulate a service interface
    trait UserDao {
        fn find_by_id(&self, id: u32) -> Option<String>;
        fn save(&mut self, user: &str) -> bool;
        fn delete(&mut self, id: u32) -> bool;
    }
    
    trait Notifier {
        fn notify(&self, event: &str, data: &str);
    }
    
    // Service that uses the interfaces
    struct UserService {
        // In real code, these would be trait objects or mock implementations
    }
    
    impl UserService {
        fn create_user(&mut self, _name: &str) -> Result<u32, String> {
            // In real code: dao.save, notifier.notify, etc.
            Ok(123)
        }
        
        fn get_user(&self, _id: u32) -> Option<String> {
            // In real code: dao.find_by_id
            Some("User(id: 123)".to_string())
        }
    }
    
    #[test]
    fn test_user_service_with_fluent_api() {
        // Setup phase - Define expected mock behavior
        let mut dao_setup = MockSetup::new("UserDao");
        dao_setup.when("find_by_id")
            .with_args(&[123])
            .returns("User(id: 123)")
            .times(1);
        
        dao_setup.when("save")
            .with_args(&["Alice"])
            .returns("true")
            .at_least_once();
        
        let mut notifier_setup = MockSetup::new("Notifier");
        notifier_setup.when("notify")
            .with_args(&["user.created", "123"])
            .times(1);
        
        // Print setup for documentation
        println!("Mock Setup:");
        for setup in dao_setup.setups() {
            println!("  {}", setup);
        }
        
        // Exercise phase - Call the system under test
        let mut service = UserService {};
        let user_id = service.create_user("Alice").unwrap();
        let _user = service.get_user(user_id);
        
        // Verify phase - Check mock interactions
        let mut dao_verify = MockVerify::new("UserDao");
        dao_verify.method("find_by_id")
            .was_called()
            .with_args(&[123])
            .once();
        
        // Simulate actual call count (in real code, the mock framework provides this)
        dao_verify.verifications_mut()[0].set_actual_calls(1);
        
        // Verify all expectations
        match dao_verify.verify_all() {
            Ok(()) => println!("✓ All verifications passed"),
            Err(errors) => {
                for error in errors {
                    eprintln!("✗ Verification failed: {}", error);
                }
                panic!("Verification failed");
            }
        }
    }
    
    #[test]
    fn test_spy_pattern() {
        // Spy records all calls without predefined expectations
        let mut notifier_spy = Spy::new("Notifier");
        
        // Simulate service calls
        notifier_spy.record("notify", vec!["user.created", "123"]);
        notifier_spy.record("notify", vec!["user.updated", "123"]);
        notifier_spy.record("email_sent", vec!["alice@example.com"]);
        
        // Verify behavior after the fact
        assert_eq!(notifier_spy.call_count("notify"), 2);
        assert_eq!(notifier_spy.call_count("email_sent"), 1);
        
        // Inspect call arguments
        let notify_calls = notifier_spy.get_calls("notify");
        assert_eq!(notify_calls.len(), 2);
        assert_eq!(notify_calls[0][0], "user.created");
        assert_eq!(notify_calls[1][0], "user.updated");
        
        // Get all calls
        let all_calls = notifier_spy.all_calls();
        assert_eq!(all_calls.len(), 3);
        
        println!("Spy recorded {} calls", all_calls.len());
        for (method, args) in all_calls {
            println!("  {}({})", method, args.join(", "));
        }
    }
    
    #[test]
    fn test_complex_argument_matching() {
        use simple_mock_helper::fluent::ArgMatcher;
        
        let mut setup = MockSetup::new("Calculator");
        
        // Use different matcher types
        setup.when("compute")
            .with_matchers(vec![
                ArgMatcher::Any,                    // First arg: anything
                ArgMatcher::GreaterThan(0),         // Second arg: > 0
                ArgMatcher::Range(1, 100),          // Third arg: 1-100
            ])
            .returns("42");
        
        println!("Setup with matchers: {}", setup.setups()[0]);
        
        // Verify that all matchers are recorded
        let matchers = setup.setups()[0].matchers();
        assert_eq!(matchers.len(), 3);
        
        match &matchers[0] {
            ArgMatcher::Any => println!("✓ First arg matches any"),
            _ => panic!("Expected Any matcher"),
        }
        
        match &matchers[1] {
            ArgMatcher::GreaterThan(0) => println!("✓ Second arg > 0"),
            _ => panic!("Expected GreaterThan matcher"),
        }
        
        match &matchers[2] {
            ArgMatcher::Range(1, 100) => println!("✓ Third arg in range 1-100"),
            _ => panic!("Expected Range matcher"),
        }
    }
    
    #[test]
    fn test_sequential_returns() {
        let mut setup = MockSetup::new("Counter");
        
        // Return different values on successive calls
        setup.when("next")
            .returns_seq(vec!["1", "2", "3", "4", "5"]);
        
        let returns = setup.setups()[0].return_values();
        assert_eq!(returns.len(), 5);
        assert_eq!(returns[0], "1");
        assert_eq!(returns[4], "5");
        
        println!("Sequential returns: {:?}", returns);
    }
    
    #[test]
    fn test_verification_failures() {
        let mut verify = MockVerify::new("UserDao");
        
        // Expect 3 calls
        verify.method("save").times(3);
        
        // But only 1 call was made
        verify.verifications_mut()[0].set_actual_calls(1);
        
        // Verification should fail
        let result = verify.verify_all();
        assert!(result.is_err());
        
        if let Err(errors) = result {
            println!("Expected verification failure:");
            for error in errors {
                println!("  ✗ {}", error);
            }
        }
    }
    
    #[test]
    fn test_multiple_method_setup() {
        let mut setup = MockSetup::new("ComplexService");
        
        // Configure multiple methods
        setup.when("authenticate").with_args(&["admin", "secret"]).returns("token123");
        setup.when("authorize").with_args(&["token123", "read"]).returns("true");
        setup.when("execute").with_args(&["token123", "query"]).returns("result");
        setup.when("logout").with_args(&["token123"]).returns("ok");
        
        assert_eq!(setup.setups().len(), 4);
        
        println!("Complex service setup:");
        for s in setup.setups() {
            println!("  {}", s);
        }
    }

    #[test]
    fn test_deep_call_chain_mocking() {
        let mut setup = MockSetup::new("Library");
        
        // Mock a deep call chain: library.getHeadLibrarian().getName()
        setup.when("getHeadLibrarian")
            .chain("getName")
            .returns("Jane Doe");
        
        // Mock another chain: company.getDepartment("Engineering").getManager().getName()
        setup.when("getDepartment")
            .chain("getManager")
            .chain("getName")
            .with_args(&["Engineering"])
            .returns("Alice Smith");
        
        assert_eq!(setup.setups().len(), 2);
        
        // Verify first chain
        let first = &setup.setups()[0];
        assert_eq!(first.method_name(), "getHeadLibrarian");
        assert_eq!(first.method_chain().len(), 1);
        assert_eq!(first.full_method_path(), "getHeadLibrarian().getName");
        
        // Verify second chain
        let second = &setup.setups()[1];
        assert_eq!(second.method_name(), "getDepartment");
        assert_eq!(second.method_chain().len(), 2);
        assert_eq!(second.full_method_path(), "getDepartment().getManager().getName");
        
        println!("Deep call chain mocking:");
        for s in setup.setups() {
            println!("  {}", s);
        }
    }
}
