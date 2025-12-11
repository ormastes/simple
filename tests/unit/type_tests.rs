//! Comprehensive type checker unit tests

use simple_parser::Parser;
use simple_type::{check, Substitution, Type, TypeChecker, TypeError};

// === Type Construction Tests ===

#[test]
fn test_type_int() {
    let ty = Type::Int;
    assert_eq!(ty, Type::Int);
}

#[test]
fn test_type_float() {
    let ty = Type::Float;
    assert_eq!(ty, Type::Float);
}

#[test]
fn test_type_bool() {
    let ty = Type::Bool;
    assert_eq!(ty, Type::Bool);
}

#[test]
fn test_type_str() {
    let ty = Type::Str;
    assert_eq!(ty, Type::Str);
}

#[test]
fn test_type_nil() {
    let ty = Type::Nil;
    assert_eq!(ty, Type::Nil);
}

#[test]
fn test_type_var() {
    let ty = Type::Var(0);
    assert_eq!(ty, Type::Var(0));
}

#[test]
fn test_type_array() {
    let ty = Type::Array(Box::new(Type::Int));
    assert!(matches!(ty, Type::Array(_)));
}

#[test]
fn test_type_tuple() {
    let ty = Type::Tuple(vec![Type::Int, Type::Bool]);
    if let Type::Tuple(types) = ty {
        assert_eq!(types.len(), 2);
    } else {
        panic!("Expected tuple type");
    }
}

#[test]
fn test_type_function() {
    let ty = Type::Function {
        params: vec![Type::Int, Type::Int],
        ret: Box::new(Type::Int),
    };
    if let Type::Function { params, ret } = ty {
        assert_eq!(params.len(), 2);
        assert_eq!(*ret, Type::Int);
    } else {
        panic!("Expected function type");
    }
}

#[test]
fn test_type_union() {
    let ty = Type::Union(vec![Type::Int, Type::Str]);
    if let Type::Union(types) = ty {
        assert_eq!(types.len(), 2);
    } else {
        panic!("Expected union type");
    }
}

#[test]
fn test_type_generic() {
    let ty = Type::Generic {
        name: "Option".to_string(),
        args: vec![Type::Int],
    };
    if let Type::Generic { name, args } = ty {
        assert_eq!(name, "Option");
        assert_eq!(args.len(), 1);
    } else {
        panic!("Expected generic type");
    }
}

#[test]
fn test_type_type_param() {
    let ty = Type::TypeParam("T".to_string());
    if let Type::TypeParam(name) = ty {
        assert_eq!(name, "T");
    } else {
        panic!("Expected type param");
    }
}

#[test]
fn test_type_named() {
    let ty = Type::Named("Point".to_string());
    if let Type::Named(name) = ty {
        assert_eq!(name, "Point");
    } else {
        panic!("Expected named type");
    }
}

#[test]
fn test_type_dict() {
    let ty = Type::Dict {
        key: Box::new(Type::Str),
        value: Box::new(Type::Int),
    };
    if let Type::Dict { key, value } = ty {
        assert_eq!(*key, Type::Str);
        assert_eq!(*value, Type::Int);
    } else {
        panic!("Expected dict type");
    }
}

#[test]
fn test_type_optional() {
    let ty = Type::Optional(Box::new(Type::Int));
    if let Type::Optional(inner) = ty {
        assert_eq!(*inner, Type::Int);
    } else {
        panic!("Expected optional type");
    }
}

#[test]
fn test_type_borrow() {
    let ty = Type::Borrow(Box::new(Type::Int));
    if let Type::Borrow(inner) = ty {
        assert_eq!(*inner, Type::Int);
    } else {
        panic!("Expected borrow type");
    }
}

#[test]
fn test_type_borrow_mut() {
    let ty = Type::BorrowMut(Box::new(Type::Int));
    if let Type::BorrowMut(inner) = ty {
        assert_eq!(*inner, Type::Int);
    } else {
        panic!("Expected mutable borrow type");
    }
}

// === Substitution Tests ===

#[test]
fn test_substitution_new() {
    let subst = Substitution::new();
    assert!(subst.get(0).is_none());
}

#[test]
fn test_substitution_insert_get() {
    let mut subst = Substitution::new();
    subst.insert(0, Type::Int);
    assert_eq!(subst.get(0), Some(&Type::Int));
}

#[test]
fn test_substitution_compose() {
    let mut subst1 = Substitution::new();
    subst1.insert(0, Type::Int);

    let mut subst2 = Substitution::new();
    subst2.insert(1, Type::Var(0));

    subst1.compose(&subst2);
    // After composition, var 1 should resolve to Int
    assert_eq!(subst1.get(1), Some(&Type::Int));
}

// === Type Apply Substitution Tests ===

#[test]
fn test_apply_subst_primitive() {
    let subst = Substitution::new();
    let ty = Type::Int;
    assert_eq!(ty.apply_subst(&subst), Type::Int);
}

#[test]
fn test_apply_subst_var_no_mapping() {
    let subst = Substitution::new();
    let ty = Type::Var(0);
    assert_eq!(ty.apply_subst(&subst), Type::Var(0));
}

#[test]
fn test_apply_subst_var_with_mapping() {
    let mut subst = Substitution::new();
    subst.insert(0, Type::Int);
    let ty = Type::Var(0);
    assert_eq!(ty.apply_subst(&subst), Type::Int);
}

#[test]
fn test_apply_subst_array() {
    let mut subst = Substitution::new();
    subst.insert(0, Type::Int);
    let ty = Type::Array(Box::new(Type::Var(0)));
    assert_eq!(ty.apply_subst(&subst), Type::Array(Box::new(Type::Int)));
}

#[test]
fn test_apply_subst_function() {
    let mut subst = Substitution::new();
    subst.insert(0, Type::Int);
    subst.insert(1, Type::Bool);
    let ty = Type::Function {
        params: vec![Type::Var(0)],
        ret: Box::new(Type::Var(1)),
    };
    let result = ty.apply_subst(&subst);
    if let Type::Function { params, ret } = result {
        assert_eq!(params[0], Type::Int);
        assert_eq!(*ret, Type::Bool);
    } else {
        panic!("Expected function type");
    }
}

#[test]
fn test_apply_subst_tuple() {
    let mut subst = Substitution::new();
    subst.insert(0, Type::Int);
    let ty = Type::Tuple(vec![Type::Var(0), Type::Bool]);
    let result = ty.apply_subst(&subst);
    if let Type::Tuple(types) = result {
        assert_eq!(types[0], Type::Int);
        assert_eq!(types[1], Type::Bool);
    } else {
        panic!("Expected tuple type");
    }
}

#[test]
fn test_apply_subst_union() {
    let mut subst = Substitution::new();
    subst.insert(0, Type::Str);
    let ty = Type::Union(vec![Type::Var(0), Type::Int]);
    let result = ty.apply_subst(&subst);
    if let Type::Union(types) = result {
        assert_eq!(types[0], Type::Str);
    } else {
        panic!("Expected union type");
    }
}

#[test]
fn test_apply_subst_generic() {
    let mut subst = Substitution::new();
    subst.insert(0, Type::Int);
    let ty = Type::Generic {
        name: "List".to_string(),
        args: vec![Type::Var(0)],
    };
    let result = ty.apply_subst(&subst);
    if let Type::Generic { args, .. } = result {
        assert_eq!(args[0], Type::Int);
    } else {
        panic!("Expected generic type");
    }
}

#[test]
fn test_apply_subst_dict() {
    let mut subst = Substitution::new();
    subst.insert(0, Type::Str);
    subst.insert(1, Type::Int);
    let ty = Type::Dict {
        key: Box::new(Type::Var(0)),
        value: Box::new(Type::Var(1)),
    };
    let result = ty.apply_subst(&subst);
    if let Type::Dict { key, value } = result {
        assert_eq!(*key, Type::Str);
        assert_eq!(*value, Type::Int);
    } else {
        panic!("Expected dict type");
    }
}

#[test]
fn test_apply_subst_optional() {
    let mut subst = Substitution::new();
    subst.insert(0, Type::Int);
    let ty = Type::Optional(Box::new(Type::Var(0)));
    assert_eq!(ty.apply_subst(&subst), Type::Optional(Box::new(Type::Int)));
}

#[test]
fn test_apply_subst_borrow() {
    let mut subst = Substitution::new();
    subst.insert(0, Type::Int);
    let ty = Type::Borrow(Box::new(Type::Var(0)));
    assert_eq!(ty.apply_subst(&subst), Type::Borrow(Box::new(Type::Int)));
}

#[test]
fn test_apply_subst_borrow_mut() {
    let mut subst = Substitution::new();
    subst.insert(0, Type::Int);
    let ty = Type::BorrowMut(Box::new(Type::Var(0)));
    assert_eq!(ty.apply_subst(&subst), Type::BorrowMut(Box::new(Type::Int)));
}

// === Contains Var Tests ===

#[test]
fn test_contains_var_primitive() {
    assert!(!Type::Int.contains_var(0));
}

#[test]
fn test_contains_var_same() {
    assert!(Type::Var(0).contains_var(0));
}

#[test]
fn test_contains_var_different() {
    assert!(!Type::Var(1).contains_var(0));
}

#[test]
fn test_contains_var_array() {
    let ty = Type::Array(Box::new(Type::Var(0)));
    assert!(ty.contains_var(0));
    assert!(!ty.contains_var(1));
}

#[test]
fn test_contains_var_function() {
    let ty = Type::Function {
        params: vec![Type::Var(0)],
        ret: Box::new(Type::Var(1)),
    };
    assert!(ty.contains_var(0));
    assert!(ty.contains_var(1));
    assert!(!ty.contains_var(2));
}

#[test]
fn test_contains_var_tuple() {
    let ty = Type::Tuple(vec![Type::Int, Type::Var(0)]);
    assert!(ty.contains_var(0));
    assert!(!ty.contains_var(1));
}

#[test]
fn test_contains_var_union() {
    let ty = Type::Union(vec![Type::Var(0), Type::Int]);
    assert!(ty.contains_var(0));
}

#[test]
fn test_contains_var_generic() {
    let ty = Type::Generic {
        name: "Option".to_string(),
        args: vec![Type::Var(0)],
    };
    assert!(ty.contains_var(0));
}

#[test]
fn test_contains_var_dict() {
    let ty = Type::Dict {
        key: Box::new(Type::Var(0)),
        value: Box::new(Type::Int),
    };
    assert!(ty.contains_var(0));

    let ty2 = Type::Dict {
        key: Box::new(Type::Str),
        value: Box::new(Type::Var(1)),
    };
    assert!(ty2.contains_var(1));
}

#[test]
fn test_contains_var_optional() {
    let ty = Type::Optional(Box::new(Type::Var(0)));
    assert!(ty.contains_var(0));
}

#[test]
fn test_contains_var_borrow() {
    let ty = Type::Borrow(Box::new(Type::Var(0)));
    assert!(ty.contains_var(0));
}

#[test]
fn test_contains_var_borrow_mut() {
    let ty = Type::BorrowMut(Box::new(Type::Var(0)));
    assert!(ty.contains_var(0));
}

// === TypeChecker Creation Tests ===

#[test]
fn test_type_checker_new() {
    let tc = TypeChecker::new();
    let _ = tc;
}

#[test]
fn test_fresh_var() {
    let mut tc = TypeChecker::new();
    let var1 = tc.fresh_var();
    let var2 = tc.fresh_var();
    // Fresh vars should have different IDs
    assert_ne!(var1, var2);
}

// === Unification Tests ===

#[test]
fn test_unify_same_primitives() {
    let mut tc = TypeChecker::new();
    assert!(tc.unify(&Type::Int, &Type::Int).is_ok());
    assert!(tc.unify(&Type::Float, &Type::Float).is_ok());
    assert!(tc.unify(&Type::Bool, &Type::Bool).is_ok());
    assert!(tc.unify(&Type::Str, &Type::Str).is_ok());
    assert!(tc.unify(&Type::Nil, &Type::Nil).is_ok());
}

#[test]
fn test_unify_different_primitives() {
    let mut tc = TypeChecker::new();
    assert!(tc.unify(&Type::Int, &Type::Bool).is_err());
    assert!(tc.unify(&Type::Str, &Type::Int).is_err());
}

#[test]
fn test_unify_var_with_type() {
    let mut tc = TypeChecker::new();
    let var = tc.fresh_var();
    assert!(tc.unify(&var, &Type::Int).is_ok());
    assert_eq!(tc.resolve(&var), Type::Int);
}

#[test]
fn test_unify_type_with_var() {
    let mut tc = TypeChecker::new();
    let var = tc.fresh_var();
    assert!(tc.unify(&Type::Int, &var).is_ok());
    assert_eq!(tc.resolve(&var), Type::Int);
}

#[test]
fn test_unify_two_vars() {
    let mut tc = TypeChecker::new();
    let var1 = tc.fresh_var();
    let var2 = tc.fresh_var();
    assert!(tc.unify(&var1, &var2).is_ok());
}

#[test]
fn test_unify_same_var() {
    let mut tc = TypeChecker::new();
    let var = tc.fresh_var();
    assert!(tc.unify(&var, &var).is_ok());
}

#[test]
fn test_unify_arrays() {
    let mut tc = TypeChecker::new();
    let arr1 = Type::Array(Box::new(Type::Int));
    let arr2 = Type::Array(Box::new(Type::Int));
    assert!(tc.unify(&arr1, &arr2).is_ok());
}

#[test]
fn test_unify_arrays_different_elem() {
    let mut tc = TypeChecker::new();
    let arr1 = Type::Array(Box::new(Type::Int));
    let arr2 = Type::Array(Box::new(Type::Bool));
    assert!(tc.unify(&arr1, &arr2).is_err());
}

#[test]
fn test_unify_tuples_same() {
    let mut tc = TypeChecker::new();
    let t1 = Type::Tuple(vec![Type::Int, Type::Bool]);
    let t2 = Type::Tuple(vec![Type::Int, Type::Bool]);
    assert!(tc.unify(&t1, &t2).is_ok());
}

#[test]
fn test_unify_tuples_different_length() {
    let mut tc = TypeChecker::new();
    let t1 = Type::Tuple(vec![Type::Int]);
    let t2 = Type::Tuple(vec![Type::Int, Type::Bool]);
    assert!(tc.unify(&t1, &t2).is_err());
}

#[test]
fn test_unify_functions_same() {
    let mut tc = TypeChecker::new();
    let f1 = Type::Function {
        params: vec![Type::Int],
        ret: Box::new(Type::Bool),
    };
    let f2 = Type::Function {
        params: vec![Type::Int],
        ret: Box::new(Type::Bool),
    };
    assert!(tc.unify(&f1, &f2).is_ok());
}

#[test]
fn test_unify_functions_different_params() {
    let mut tc = TypeChecker::new();
    let f1 = Type::Function {
        params: vec![Type::Int],
        ret: Box::new(Type::Bool),
    };
    let f2 = Type::Function {
        params: vec![Type::Str],
        ret: Box::new(Type::Bool),
    };
    assert!(tc.unify(&f1, &f2).is_err());
}

#[test]
fn test_unify_generics_same() {
    let mut tc = TypeChecker::new();
    let g1 = Type::Generic {
        name: "Option".to_string(),
        args: vec![Type::Int],
    };
    let g2 = Type::Generic {
        name: "Option".to_string(),
        args: vec![Type::Int],
    };
    assert!(tc.unify(&g1, &g2).is_ok());
}

#[test]
fn test_unify_generics_different_name() {
    let mut tc = TypeChecker::new();
    let g1 = Type::Generic {
        name: "Option".to_string(),
        args: vec![Type::Int],
    };
    let g2 = Type::Generic {
        name: "Result".to_string(),
        args: vec![Type::Int],
    };
    assert!(tc.unify(&g1, &g2).is_err());
}

#[test]
fn test_unify_optional_same() {
    let mut tc = TypeChecker::new();
    let o1 = Type::Optional(Box::new(Type::Int));
    let o2 = Type::Optional(Box::new(Type::Int));
    assert!(tc.unify(&o1, &o2).is_ok());
}

#[test]
fn test_unify_dict_same() {
    let mut tc = TypeChecker::new();
    let d1 = Type::Dict {
        key: Box::new(Type::Str),
        value: Box::new(Type::Int),
    };
    let d2 = Type::Dict {
        key: Box::new(Type::Str),
        value: Box::new(Type::Int),
    };
    assert!(tc.unify(&d1, &d2).is_ok());
}

#[test]
fn test_unify_named_same() {
    let mut tc = TypeChecker::new();
    let n1 = Type::Named("Point".to_string());
    let n2 = Type::Named("Point".to_string());
    assert!(tc.unify(&n1, &n2).is_ok());
}

#[test]
fn test_unify_named_different() {
    let mut tc = TypeChecker::new();
    let n1 = Type::Named("Point".to_string());
    let n2 = Type::Named("Vector".to_string());
    assert!(tc.unify(&n1, &n2).is_err());
}

#[test]
fn test_unify_type_param_same() {
    let mut tc = TypeChecker::new();
    let t1 = Type::TypeParam("T".to_string());
    let t2 = Type::TypeParam("T".to_string());
    assert!(tc.unify(&t1, &t2).is_ok());
}

