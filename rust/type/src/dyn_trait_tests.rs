// Unit tests for dyn trait type inference (embedded in lib for simpler testing)

#[cfg(test)]
mod dyn_trait_unit_tests {
    use crate::{Type, TypeChecker};

    #[test]
    fn test_dyn_trait_unify_same() {
        let mut checker = TypeChecker::new();
        let t1 = Type::DynTrait("Logger".into());
        let t2 = Type::DynTrait("Logger".into());
        assert!(checker.unify(&t1, &t2).is_ok());
    }

    #[test]
    fn test_dyn_trait_unify_different() {
        let mut checker = TypeChecker::new();
        let t1 = Type::DynTrait("Logger".into());
        let t2 = Type::DynTrait("Drawable".into());
        assert!(checker.unify(&t1, &t2).is_err());
    }

    #[test]
    fn test_dyn_trait_vs_int() {
        let mut checker = TypeChecker::new();
        let t1 = Type::DynTrait("Logger".into());
        let t2 = Type::Int;
        assert!(checker.unify(&t1, &t2).is_err());
    }

    #[test]
    fn test_dyn_trait_in_array() {
        let dyn_logger = Type::DynTrait("Logger".into());
        let array_ty = Type::Array(Box::new(dyn_logger.clone()));
        match &array_ty {
            Type::Array(elem) => assert_eq!(**elem, dyn_logger),
            _ => panic!("Expected Array"),
        }
    }

    #[test]
    fn test_dyn_trait_in_optional() {
        let dyn_logger = Type::DynTrait("Logger".into());
        let opt_ty = Type::Optional(Box::new(dyn_logger.clone()));
        match &opt_ty {
            Type::Optional(inner) => assert_eq!(**inner, dyn_logger),
            _ => panic!("Expected Optional"),
        }
    }

    #[test]
    fn test_dyn_trait_compatible_same() {
        let checker = TypeChecker::new();
        let t1 = Type::DynTrait("Logger".into());
        let t2 = Type::DynTrait("Logger".into());
        assert!(checker.types_compatible(&t1, &t2));
    }

    #[test]
    fn test_dyn_trait_not_compatible_different() {
        let checker = TypeChecker::new();
        let t1 = Type::DynTrait("Logger".into());
        let t2 = Type::DynTrait("Drawable".into());
        assert!(!checker.types_compatible(&t1, &t2));
    }
}
