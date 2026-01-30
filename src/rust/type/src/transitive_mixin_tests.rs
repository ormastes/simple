// Unit tests for transitive mixin resolution (embedded in lib for simpler testing)

#[cfg(test)]
mod transitive_mixin_unit_tests {
    use crate::{Type, TypeChecker, MixinInfo};

    fn create_base() -> MixinInfo {
        MixinInfo {
            name: "Base".into(),
            type_params: vec![],
            fields: vec![("id".into(), Type::Int)],
            methods: vec![],
            required_traits: vec![],
            required_mixins: vec![],
            required_methods: vec![],
        }
    }

    fn create_timestamped() -> MixinInfo {
        MixinInfo {
            name: "Timestamped".into(),
            type_params: vec![],
            fields: vec![("created_at".into(), Type::Int), ("updated_at".into(), Type::Int)],
            methods: vec![],
            required_traits: vec![],
            required_mixins: vec!["Base".into()],
            required_methods: vec![],
        }
    }

    fn create_versioned() -> MixinInfo {
        MixinInfo {
            name: "Versioned".into(),
            type_params: vec![],
            fields: vec![("version".into(), Type::Int)],
            methods: vec![],
            required_traits: vec![],
            required_mixins: vec!["Timestamped".into()],
            required_methods: vec![],
        }
    }

    #[test]
    fn test_resolve_empty() {
        let checker = TypeChecker::new();
        let result = checker.resolve_transitive_mixins(&[]);
        assert_eq!(result, Vec::<String>::new());
    }

    #[test]
    fn test_resolve_single_no_deps() {
        let mut checker = TypeChecker::new();
        checker.mixins.insert("Base".into(), create_base());
        let result = checker.resolve_transitive_mixins(&["Base".into()]);
        assert_eq!(result, vec!["Base"]);
    }

    #[test]
    fn test_resolve_two_level() {
        let mut checker = TypeChecker::new();
        checker.mixins.insert("Base".into(), create_base());
        checker.mixins.insert("Timestamped".into(), create_timestamped());
        let result = checker.resolve_transitive_mixins(&["Timestamped".into()]);
        assert_eq!(result.len(), 2);
        assert!(result.contains(&"Base".to_string()));
        assert!(result.contains(&"Timestamped".to_string()));
    }

    #[test]
    fn test_resolve_three_level() {
        let mut checker = TypeChecker::new();
        checker.mixins.insert("Base".into(), create_base());
        checker.mixins.insert("Timestamped".into(), create_timestamped());
        checker.mixins.insert("Versioned".into(), create_versioned());
        let result = checker.resolve_transitive_mixins(&["Versioned".into()]);
        assert_eq!(result.len(), 3);
        assert!(result.contains(&"Base".to_string()));
        assert!(result.contains(&"Timestamped".to_string()));
        assert!(result.contains(&"Versioned".to_string()));
    }

    #[test]
    fn test_diamond_dedup() {
        let mut checker = TypeChecker::new();
        let base = create_base();
        let left = MixinInfo {
            name: "Left".into(),
            type_params: vec![],
            fields: vec![("left_field".into(), Type::Int)],
            methods: vec![],
            required_traits: vec![],
            required_mixins: vec!["Base".into()],
            required_methods: vec![],
        };
        let right = MixinInfo {
            name: "Right".into(),
            type_params: vec![],
            fields: vec![("right_field".into(), Type::Str)],
            methods: vec![],
            required_traits: vec![],
            required_mixins: vec!["Base".into()],
            required_methods: vec![],
        };
        let combined = MixinInfo {
            name: "Combined".into(),
            type_params: vec![],
            fields: vec![],
            methods: vec![],
            required_traits: vec![],
            required_mixins: vec!["Left".into(), "Right".into()],
            required_methods: vec![],
        };

        checker.mixins.insert("Base".into(), base);
        checker.mixins.insert("Left".into(), left);
        checker.mixins.insert("Right".into(), right);
        checker.mixins.insert("Combined".into(), combined);

        let result = checker.resolve_transitive_mixins(&["Combined".into()]);
        assert_eq!(result.len(), 4);
        let base_count = result.iter().filter(|x| *x == "Base").count();
        assert_eq!(base_count, 1, "Base should appear once (diamond dedup)");
    }

    #[test]
    fn test_mixin_not_found() {
        let checker = TypeChecker::new();
        let result = checker.resolve_transitive_mixins(&["NonExistent".into()]);
        assert!(result.is_empty());
    }

    #[test]
    fn test_instantiate_preserves_required_mixins() {
        let mixin = MixinInfo {
            name: "Test".into(),
            type_params: vec!["T".into()],
            fields: vec![("field".into(), Type::TypeParam("T".into()))],
            methods: vec![],
            required_traits: vec!["Show".into()],
            required_mixins: vec!["Base".into()],
            required_methods: vec![],
        };

        let inst = mixin.instantiate(&[Type::Int]).unwrap();
        assert_eq!(inst.required_mixins, vec!["Base"]);
        assert_eq!(inst.required_traits, vec!["Show"]);
    }
}
