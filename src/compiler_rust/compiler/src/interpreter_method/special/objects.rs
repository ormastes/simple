//! Trait object and constructor methods

// Special type methods: Unit, Option, Result, Mock, Future, Channel, ThreadPool, TraitObject, Object, Constructor

use std::sync::Arc;
use crate::error::{codes, CompileError, ErrorContext};
use crate::interpreter::{
    evaluate_expr, exec_function_with_bound_args, find_and_exec_method, Enums, ImplMethods, BLOCK_SCOPED_ENUMS,
    GLOBAL_ENUMS, TRAIT_IMPLS,
};
use crate::value::{Env, OptionVariant, ResultVariant, SpecialEnumType, Value};
use simple_parser::ast::{Argument, ClassDef, FunctionDef, Type};
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};

// Import IN_NEW_METHOD from interpreter_call module
use crate::interpreter::IN_NEW_METHOD;

/// Collect every generic type parameter that is in scope for `func` when it is
/// declared inside a class: the class's own parameters (`class Foo<T>`) plus the
/// method's own (`static fn bar<U>(...)`).
fn constructor_scope_type_params(class_generic_params: &[String], func: &FunctionDef) -> HashSet<String> {
    let mut params: HashSet<String> = class_generic_params.iter().cloned().collect();
    params.extend(func.generic_params.iter().cloned());
    params
}

/// True when `ty` is (or contains) a reference to an in-scope generic type
/// parameter, i.e. the declared type is a placeholder rather than a nominal type.
fn constructor_type_mentions_param(ty: &Type, type_params: &HashSet<String>) -> bool {
    match ty {
        Type::Simple(name) => type_params.contains(name),
        Type::Generic { name, args } => {
            type_params.contains(name) || args.iter().any(|arg| constructor_type_mentions_param(arg, type_params))
        }
        Type::Array { element, .. } => constructor_type_mentions_param(element, type_params),
        _ => false,
    }
}

fn constructor_value_type_matches_name(value: &Value, expected: &str, type_params: &HashSet<String>) -> bool {
    // An in-scope generic type parameter is NOT a nominal type: `static fn
    // from_data(data: [T])` on `class PureTensor<T>` declares `T` as a
    // placeholder that any argument instantiates. Scoring it like a class name
    // made `value.type_name() == "T"` false for every possible argument, so
    // constructor_overload_score returned None, the candidate list came out
    // empty and the call was reported as "unknown static method from_data on
    // class PureTensor" — as if the method did not exist at all. Statics whose
    // signature mentioned no type parameter (`zeros`/`ones`/`randn`) resolved
    // fine, which is exactly the asymmetry recorded in bug doc
    // generic_static_method_type_param_unresolved_2026-07-25.md. Treat a type
    // parameter as a wildcard here; the scorer below still prefers a concrete
    // nominal match over a wildcard one so real overloads are not disturbed.
    if type_params.contains(expected) {
        return true;
    }
    match value {
        // A concrete object's class name rarely equals the declared parameter
        // type verbatim when the parameter is a trait/interface (e.g. `fn
        // new(device: BlockDevice)` called with a `Fat32LfnMockBlockDevice`
        // that does `impl BlockDevice for Fat32LfnMockBlockDevice`). Fall back
        // to TRAIT_IMPLS so trait-typed constructor params accept any
        // concrete type that implements the trait, instead of only a class
        // literally named after the trait. Without this, EVERY static
        // constructor taking a trait-typed parameter fails overload scoring
        // (see bug doc fat32_core_lfn_static_new_trait_param_2026-07-20.md).
        Value::Object { class, .. } => {
            class == expected
                || TRAIT_IMPLS.with(|cell| cell.borrow().contains_key(&(expected.to_string(), class.clone())))
        }
        Value::Enum { enum_name, .. } => enum_name == expected,
        Value::Str(_) => matches!(expected, "str" | "text" | "String" | "Str"),
        _ => value.type_name() == expected || value.matches_type(expected),
    }
}

fn constructor_value_matches_type(value: &Value, ty: &Type, type_params: &HashSet<String>) -> bool {
    match ty {
        Type::Generic { name, args } if matches!(name.as_str(), "List" | "Array" | "Vec") && args.len() == 1 => {
            match value {
                Value::Array(items) => items
                    .iter()
                    .all(|item| constructor_value_matches_type(item, &args[0], type_params)),
                Value::FrozenArray(items) => items
                    .iter()
                    .all(|item| constructor_value_matches_type(item, &args[0], type_params)),
                Value::Tuple(items) => items
                    .iter()
                    .all(|item| constructor_value_matches_type(item, &args[0], type_params)),
                _ => false,
            }
        }
        Type::Simple(name) | Type::Generic { name, .. } => {
            constructor_value_type_matches_name(value, name, type_params)
        }
        Type::Array { element, .. } => match value {
            Value::Array(items) => items
                .iter()
                .all(|item| constructor_value_matches_type(item, element, type_params)),
            Value::FrozenArray(items) => items
                .iter()
                .all(|item| constructor_value_matches_type(item, element, type_params)),
            Value::Tuple(items) => items
                .iter()
                .all(|item| constructor_value_matches_type(item, element, type_params)),
            _ => false,
        },
        _ => true,
    }
}

fn constructor_overload_score(func: &FunctionDef, values: &[Value], class_generic_params: &[String]) -> Option<usize> {
    let type_params = constructor_scope_type_params(class_generic_params, func);
    let total_params = func.params.len();
    let required_params = func.params.iter().filter(|p| p.default.is_none()).count();
    let provided = values.len();

    // Accept calls where required_params <= provided <= total_params.
    // Exact-count matches score higher than default-fill matches (100-point bonus).
    if provided < required_params || provided > total_params {
        return None;
    }

    let mut score = if provided == total_params { 100usize } else { 0usize };
    for (param, value) in func.params.iter().zip(values.iter()) {
        if let Some(ty) = &param.ty {
            if !constructor_value_matches_type(value, ty, &type_params) {
                return None;
            }
            // A position matched through a generic type parameter is a weaker
            // fit than a concrete nominal match, so a `[f64]` overload still
            // beats a `[T]` one at the same position.
            score += if constructor_type_mentions_param(ty, &type_params) {
                1
            } else {
                match ty {
                    Type::Array { .. } => 4,
                    Type::Generic { name, args }
                        if matches!(name.as_str(), "List" | "Array" | "Vec") && args.len() == 1 =>
                    {
                        4
                    }
                    Type::Simple(_) | Type::Generic { .. } => 2,
                    _ => 1,
                }
            };
        }
    }
    Some(score)
}

#[allow(clippy::borrowed_box, clippy::too_many_arguments)] // reason: Box<dyn Trait> dispatch with ABI-locked entry; refactoring deferred
pub fn handle_trait_object_methods(
    trait_name: &str,
    inner: &Box<Value>,
    method: &str,
    args: &[Argument],
    env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Option<Value>, CompileError> {
    use crate::interpreter::INTERFACE_BINDINGS;

    // Check if there's an interface binding for static polymorphism
    let bound_impl = INTERFACE_BINDINGS.with(|bindings| bindings.borrow().get(trait_name).cloned());

    // Extract the inner value's class/type
    if let Value::Object { class, fields } = inner.as_ref() {
        // If there's a binding, verify the inner object matches the bound type
        // and use static dispatch to the bound implementation
        if let Some(ref bound_type) = bound_impl {
            if class != bound_type {
                // Inner type doesn't match binding - this shouldn't happen in well-typed code
                // Fall back to normal dynamic dispatch
            }
            // Static dispatch: method lookup on the bound implementation type
            if let Some(result) = find_and_exec_method(
                method,
                args,
                bound_type,
                fields,
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )? {
                return Ok(Some(result));
            }
        }

        // Dynamic dispatch: method lookup on the actual inner object type
        if let Some(result) = find_and_exec_method(
            method,
            args,
            class,
            fields,
            env,
            functions,
            classes,
            enums,
            impl_methods,
        )? {
            return Ok(Some(result));
        }
        return Err(crate::error::factory::trait_method_not_found(method, trait_name, class));
    }
    Err(crate::error::factory::trait_inner_not_object(method, trait_name))
}

/// Handle Constructor static method calls
#[allow(clippy::too_many_arguments)] // reason: ABI-locked or codegen entry signature; refactoring would break caller contract
pub fn handle_constructor_methods(
    class_name: &str,
    method: &str,
    args: &[Argument],
    env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Option<Value>, CompileError> {
    if let Some(class_def) = classes.get(class_name).cloned() {
        let evaluated_args: Vec<(Option<String>, Value)> = args
            .iter()
            .map(|arg| {
                evaluate_expr(&arg.value, env, functions, classes, enums, impl_methods)
                    .map(|value| (arg.name.clone(), value))
            })
            .collect::<Result<Vec<_>, _>>()?;
        let positional_values: Vec<Value> = evaluated_args.iter().map(|(_, value)| value.clone()).collect();
        let mut candidates: Vec<&FunctionDef> = class_def
            .methods
            .iter()
            .filter(|m| m.name == method && (m.is_static || !m.params.iter().any(|p| p.name == "self")))
            .collect();
        if let Some(extra_methods) = impl_methods.get(class_name) {
            candidates.extend(
                extra_methods
                    .iter()
                    .filter(|m| m.name == method && (m.is_static || !m.params.iter().any(|p| p.name == "self")))
                    .map(|m| m.as_ref()),
            );
        }
        let scored_method = candidates
            .iter()
            .copied()
            .filter_map(|candidate| {
                constructor_overload_score(candidate, &positional_values, &class_def.generic_params)
                    .map(|score| (score, candidate))
            })
            .max_by_key(|(score, _)| *score)
            .map(|(_, candidate)| candidate);
        let arity_matches: Vec<&FunctionDef> = candidates
            .iter()
            .copied()
            .filter(|candidate| {
                let required = candidate.params.iter().filter(|param| param.default.is_none()).count();
                required <= positional_values.len() && positional_values.len() <= candidate.params.len()
            })
            .collect();
        if let Some(method_def) = scored_method.or_else(|| {
            // Runtime aliases and values narrowed from `T?` do not retain enough
            // nominal metadata for scoring. One distinct arity signature is
            // unambiguous (the registries may contain the same impl twice).
            arity_matches
                .first()
                .copied()
                .filter(|first| arity_matches.iter().all(|candidate| candidate.params == first.params))
        }) {
            // Execute without self - start with empty local_env to avoid shadowing defaults
            let mut local_env: Env = Env::new();
            let mut positional_idx = 0;

            // Bind provided arguments
            for (arg_name, val) in evaluated_args {
                if let Some(name) = arg_name {
                    local_env.insert(name, val);
                } else if positional_idx < method_def.params.len() {
                    let param = &method_def.params[positional_idx];
                    local_env.insert(param.name.clone(), val);
                    positional_idx += 1;
                }
            }

            // Bind default values for remaining parameters using an empty scope
            // to prevent caller's variables from shadowing defaults
            let mut empty_env: Env = Env::new();
            for param in &method_def.params {
                if !local_env.contains_key(&param.name) {
                    if let Some(default_expr) = &param.default {
                        let default_val =
                            evaluate_expr(default_expr, &mut empty_env, functions, classes, enums, impl_methods)?;
                        local_env.insert(param.name.clone(), default_val);
                    }
                }
            }

            // If this is the `new` method, mark it to prevent recursion when the body
            // calls the class constructor (e.g., `ClassName(args)` inside `new()`)
            let is_new_method = method == "new";
            if is_new_method {
                IN_NEW_METHOD.with(|set| set.borrow_mut().insert(class_name.to_string()));
            }

            let result = exec_function_with_bound_args(
                method_def,
                local_env.to_map(),
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )
            .map(Some);

            // Remove from tracking set
            if is_new_method {
                IN_NEW_METHOD.with(|set| set.borrow_mut().remove(class_name));
            }

            return result;
        }

        // No matching static method on the class. `class_name` may ALSO be a
        // genuine enum whose name collides with an unrelated class/struct of
        // the same name -- e.g. `struct SdnValue:` (src/compiler/70.backend/
        // backend_types.spl, src/compiler/80.driver/init.spl) vs the real
        // `enum SdnValue:` (src/lib/common/sdn/value.spl): both get loaded
        // into the interpreter's global `classes`/`enums` registries, so
        // `SdnValue.Int(42)` resolves its receiver to `Value::Constructor`
        // (class wins identifier resolution, see `interpreter/expr/
        // literals.rs`'s `Expr::Identifier` handling) even though `Int` is
        // only a valid variant on the enum, never a static method on the
        // colliding class. This mirrors the collision class already fixed
        // for `use_bare_module_fallback` in `interpreter_method/mod.rs` (see
        // bug doc hir_stmt_expr_payload_extraction_nil_2026-07-17.md, Wall
        // 2) but for the constructor-call failure path instead: only taken
        // when the class genuinely has no matching static method AND a
        // same-named enum genuinely declares `method` as a variant, so real
        // static-method resolution is never shadowed.
        let enum_def = enums
            .get(class_name)
            .cloned()
            .or_else(|| BLOCK_SCOPED_ENUMS.with(|cell| cell.borrow().get(class_name).cloned()))
            .or_else(|| GLOBAL_ENUMS.with(|cell| cell.borrow().get(class_name).cloned()));
        if let Some(enum_def) = enum_def {
            if let Some(variant) = enum_def.variants.iter().find(|v| v.name == method) {
                let has_fields = variant.fields.as_ref().is_some_and(|f| !f.is_empty());
                let payload = if !has_fields && positional_values.is_empty() {
                    None
                } else if positional_values.len() == 1 {
                    Some(Box::new(positional_values[0].clone()))
                } else if positional_values.is_empty() {
                    None
                } else {
                    Some(Box::new(Value::Tuple(positional_values.clone())))
                };
                return Ok(Some(Value::Enum {
                    enum_name: class_name.to_string(),
                    variant: method.to_string(),
                    payload,
                }));
            }
        }

        // Collect available static methods for suggestion
        let available: Vec<&str> = class_def
            .methods
            .iter()
            .filter(|m| !m.params.iter().any(|p| p.name == "self"))
            .map(|m| m.name.as_str())
            .collect();
        let mut msg = format!("unknown static method {method} on class {class_name}");
        if let Some(suggestion) = crate::error::typo::format_suggestion(method, available) {
            msg.push_str(&format!("; {}", suggestion));
        }
        let ctx = ErrorContext::new()
            .with_code(codes::UNKNOWN_METHOD)
            .with_help("check that the method exists and is spelled correctly");
        return Err(CompileError::semantic_with_context(msg, ctx));
    }
    // No class by this name: before erroring, try qualified ENUM variant
    // construction (`EnumName.Variant(args)`) against the enum registries —
    // the same fallback the found-class branch above performs. Without this,
    // a qualified constructor whose enum has no same-named class (notably the
    // builtin `Result.Ok(...)` / `Option.Some(...)` inside imported modules,
    // e.g. bencode_decode_value) died here with "unknown class Result",
    // making every Result-wrapped API untestable under the forced-interpret
    // test lane.
    let enum_def = enums
        .get(class_name)
        .cloned()
        .or_else(|| BLOCK_SCOPED_ENUMS.with(|cell| cell.borrow().get(class_name).cloned()))
        .or_else(|| GLOBAL_ENUMS.with(|cell| cell.borrow().get(class_name).cloned()));
    if let Some(enum_def) = enum_def {
        if let Some(variant) = enum_def.variants.iter().find(|v| v.name == method) {
            // Args are still unevaluated on this no-class path.
            let mut variant_values: Vec<Value> = Vec::with_capacity(args.len());
            for arg in args {
                variant_values.push(evaluate_expr(&arg.value, env, functions, classes, enums, impl_methods)?);
            }
            let has_fields = variant.fields.as_ref().is_some_and(|f| !f.is_empty());
            let payload = if !has_fields && variant_values.is_empty() {
                None
            } else if variant_values.len() == 1 {
                Some(Box::new(variant_values[0].clone()))
            } else if variant_values.is_empty() {
                None
            } else {
                Some(Box::new(Value::Tuple(variant_values)))
            };
            return Ok(Some(Value::Enum {
                enum_name: class_name.to_string(),
                variant: method.to_string(),
                payload,
            }));
        }
    }

    // Collect available classes for suggestion
    let available: Vec<&str> = classes.keys().map(|s| s.as_str()).collect();
    let mut msg = format!("unknown class {class_name}");
    if let Some(suggestion) = crate::error::typo::format_suggestion(class_name, available) {
        msg.push_str(&format!("; {}", suggestion));
    }
    let ctx = ErrorContext::new()
        .with_code(codes::UNKNOWN_CLASS)
        .with_help("check that the class exists and is spelled correctly");
    Err(CompileError::semantic_with_context(msg, ctx))
}

#[cfg(test)]
mod tests {
    use crate::interpreter::evaluate_module;
    use simple_parser::Parser;

    /// Run source, return exit code (i32). `main = <expr>` sets exit code.
    fn eval_exit(source: &str) -> i32 {
        let mut parser = Parser::new(source);
        let module = parser.parse().expect("parse");
        evaluate_module(&module.items).expect("eval")
    }

    fn eval_err(source: &str) -> bool {
        let mut parser = Parser::new(source);
        let module = parser.parse().expect("parse");
        evaluate_module(&module.items).is_err()
    }

    // Regression: static method with default param called with fewer args must not
    // produce "unknown static method". Bug: constructor_overload_score required exact
    // arg-count match, ignoring default parameter values.
    #[test]
    fn static_method_with_default_param_called_with_fewer_args() {
        let result = eval_exit(
            r#"
class Probe:
    static fn make(a: i64, b: i64 = 0) -> i64:
        a + b
main = Probe.make(5)
"#,
        );
        assert_eq!(result, 5, "make(5) should use default b=0, returning 5");
    }

    // Regression: a static constructor taking a trait-typed parameter must
    // accept any concrete argument that implements the trait, not only a
    // value whose class is literally named after the trait. Before this fix,
    // `constructor_value_type_matches_name` compared `class == expected`
    // directly for `Value::Object` with no TRAIT_IMPLS fallback, so EVERY
    // static `new` with a trait-typed param failed overload scoring and
    // reported "unknown static method new on class ...". See bug doc
    // fat32_core_lfn_static_new_trait_param_2026-07-20.md.
    #[test]
    fn static_constructor_accepts_trait_typed_argument() {
        let result = eval_exit(
            r#"
trait Speaker:
    fn speak() -> i64

class Dog:
    x: i64

impl Speaker for Dog:
    fn speak() -> i64:
        1

class Handler:
    d: Speaker

impl Handler:
    static fn new(d: Speaker) -> i64:
        42

main = Handler.new(Dog(x: 0))
"#,
        );
        assert_eq!(
            result, 42,
            "Handler.new(Dog(..)) should resolve via the Speaker trait impl, not fail with unknown static method"
        );
    }

    #[test]
    fn static_method_accepts_type_alias_and_narrowed_optional_arguments() {
        let result = eval_exit(
            r#"
type Operation = text

class Descriptor:
    value: Operation

class Request:
    descriptor: Descriptor
    operation: Operation

impl Request:
    static fn create(descriptor: Descriptor, operation: Operation) -> i64:
        if descriptor.value == operation: 42 else: 0

fn find_descriptor() -> Descriptor?:
    Descriptor(value: "list")

val descriptor = find_descriptor()
if descriptor == nil:
    main = 0
else:
    main = Request.create(descriptor, "list")
"#,
        );
        assert_eq!(result, 42);
    }

    // Exact-count call still works and is preferred over default-fill overload.
    #[test]
    fn static_method_exact_count_still_works() {
        let result = eval_exit(
            r#"
class Probe:
    static fn make(a: i64, b: i64 = 0) -> i64:
        a + b
main = Probe.make(3, 4)
"#,
        );
        assert_eq!(result, 7, "make(3, 4) should return 7");
    }

    // Exact match beats default-fill when both overloads could match.
    #[test]
    fn exact_match_overload_preferred_over_default_fill() {
        // Two overloads: make(a) and make(a, b=0).
        // Calling make(5) should prefer the 1-param exact overload (score 100+2=102)
        // over the 2-param default-fill overload (score 0+2=2).
        let result = eval_exit(
            r#"
class Probe:
    static fn make(a: i64) -> i64:
        a * 10
    static fn make(a: i64, b: i64 = 0) -> i64:
        a + b
main = Probe.make(5)
"#,
        );
        assert_eq!(result, 50, "exact 1-param overload should win: 5*10=50");
    }

    // Too-few args (all required) must still error.
    #[test]
    fn static_method_too_few_required_args_errors() {
        assert!(
            eval_err(
                r#"
class Probe:
    static fn make(a: i64, b: i64) -> i64:
        a + b
main = Probe.make(5)
"#
            ),
            "calling make(5) when both params are required must error"
        );
    }

    // Too-many args must still error.
    #[test]
    fn static_method_too_many_args_errors() {
        assert!(
            eval_err(
                r#"
class Probe:
    static fn make(a: i64) -> i64:
        a
main = Probe.make(1, 2)
"#
            ),
            "calling make(1, 2) when only 1 param exists must error"
        );
    }
}
