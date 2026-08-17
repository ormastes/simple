// Method call dispatcher - delegates to type-specific handlers

pub(crate) mod collections;
mod primitives;
mod special;

use super::{
    eval_arg, eval_arg_int, eval_arg_usize, evaluate_expr, exec_function, exec_function_with_captured_env,
    exec_function_with_values, find_and_exec_method, instantiate_class, try_method_missing, Enums, ImplMethods,
    BITFIELDS, BLANKET_IMPL_METHODS, BLOCK_SCOPED_ENUMS, GLOBAL_ENUMS, GLOBAL_IMPL_METHODS, TRAIT_IMPLS,
};
use crate::error::{codes, typo, CompileError, ErrorContext};
use crate::value::{format_f32_display, Env, Value};
use simple_parser::ast::{Argument, ClassDef, Expr, FunctionDef};
use std::cell::RefCell;
use std::cmp::Ordering;
use std::collections::HashMap;
use std::sync::Arc;

/// Byte offset of the first byte >= 0x80, or `bytes.len()` when all-ASCII.
/// Word-at-a-time so an all-ASCII document costs ~len/8 iterations.
fn first_non_ascii(bytes: &[u8]) -> usize {
    let mut i = 0usize;
    while i + 8 <= bytes.len() {
        let w = u64::from_ne_bytes(bytes[i..i + 8].try_into().unwrap());
        if w & 0x8080_8080_8080_8080 != 0 {
            break;
        }
        i += 8;
    }
    while i < bytes.len() && bytes[i] < 0x80 {
        i += 1;
    }
    i
}

// Memo for `char_code_at`'s ASCII fast path. The interpreter's strings are
// `Arc<String>` with no spare header bits (unlike the two native runtimes, which
// cache the same fact in the string header), so the answer is memoized here,
// keyed on Arc identity.
//
// Soundness: each slot holds its own `Arc` clone, which keeps that allocation
// alive, so a pointer can never be recycled under a live entry -- `Arc::ptr_eq`
// therefore cannot alias two different strings. Strings are immutable, so a hit
// stays valid. 4 slots (round-robin) rather than 1 so that alternating between a
// couple of documents does not thrash back to a rescan on every call.
const ASCII_MEMO_SLOTS: usize = 4;

thread_local! {
    static ASCII_MEMO: RefCell<(Vec<(Arc<String>, bool)>, usize)> =
        const { RefCell::new((Vec::new(), 0)) };
}

/// True when `s` contains no byte >= 0x80. Memoized per string allocation.
fn shared_text_is_ascii(s: &Arc<String>) -> bool {
    ASCII_MEMO.with(|cell| {
        let mut m = cell.borrow_mut();
        let (slots, next) = &mut *m;
        for (cached, is_ascii) in slots.iter() {
            if Arc::ptr_eq(cached, s) {
                return *is_ascii;
            }
        }
        let is_ascii = first_non_ascii(s.as_bytes()) == s.len();
        if slots.len() < ASCII_MEMO_SLOTS {
            slots.push((Arc::clone(s), is_ascii));
        } else {
            slots[*next] = (Arc::clone(s), is_ascii);
            *next = (*next + 1) % ASCII_MEMO_SLOTS;
        }
        is_ascii
    })
}

/// Drop the `char_code_at` ASCII memo, releasing the `Arc` clones it holds.
pub fn clear_ascii_memo() {
    ASCII_MEMO.with(|cell| {
        let mut m = cell.borrow_mut();
        m.0.clear();
        m.1 = 0;
    });
}

// Thread-local storage for pinned strings used by the "ptr" method on strings.
// Strings are kept alive here so that raw pointers returned to SFFI/codegen remain valid.
// Call `clear_pinned_strings()` between test runs or when the interpreter resets to reclaim memory.
thread_local! {
    static PINNED_STRINGS: RefCell<Vec<String>> = const { RefCell::new(Vec::new()) };
}

/// Clear the thread-local pinned-string cache to free memory.
pub fn clear_pinned_strings() {
    PINNED_STRINGS.with(|cell| {
        cell.borrow_mut().clear();
    });
}

fn numeric_ordering(left: &Value, right: &Value) -> Option<Ordering> {
    match (left, right) {
        (Value::Int(a), Value::Int(b)) => Some(a.cmp(b)),
        (Value::UInt { value: a, .. }, Value::UInt { value: b, .. }) => Some(a.cmp(b)),
        (Value::Int(a), Value::UInt { value: b, .. }) => {
            if *a < 0 {
                Some(Ordering::Less)
            } else {
                Some((*a as u64).cmp(b))
            }
        }
        (Value::UInt { value: a, .. }, Value::Int(b)) => {
            if *b < 0 {
                Some(Ordering::Greater)
            } else {
                Some(a.cmp(&(*b as u64)))
            }
        }
        (Value::Float(a), Value::Float(b)) => a.partial_cmp(b),
        (Value::Float32(a), Value::Float32(b)) => a.partial_cmp(b),
        (Value::Float(a), Value::Float32(b)) => a.partial_cmp(&(*b as f64)),
        (Value::Float32(a), Value::Float(b)) => (*a as f64).partial_cmp(b),
        (Value::Float(a), b) => a.partial_cmp(&numeric_as_f64(b)?),
        (a, Value::Float(b)) => numeric_as_f64(a)?.partial_cmp(b),
        (Value::Float32(a), b) => (*a as f64).partial_cmp(&numeric_as_f64(b)?),
        (a, Value::Float32(b)) => numeric_as_f64(a)?.partial_cmp(&(*b as f64)),
        _ => None,
    }
}

fn numeric_as_f64(value: &Value) -> Option<f64> {
    match value {
        Value::Int(i) => Some(*i as f64),
        Value::UInt { value, .. } => Some(*value as f64),
        Value::Float(f) => Some(*f),
        Value::Float32(f) => Some(*f as f64),
        _ => None,
    }
}

#[allow(clippy::too_many_arguments)] // reason: mirrors the method dispatcher ABI.
fn try_bare_some_option_method(
    recv_val: &Value,
    method: &str,
    args: &[Argument],
    env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Option<Value>, CompileError> {
    let payload = Some(Box::new(recv_val.clone()));
    let option_val = Value::Enum {
        enum_name: "Option".to_string(),
        variant: "Some".to_string(),
        payload: payload.clone(),
    };
    special::handle_option_methods(
        &option_val,
        "Option",
        "Some",
        &payload,
        method,
        args,
        env,
        functions,
        classes,
        enums,
        impl_methods,
    )
}

// Re-export the with-self-update functions
pub(crate) use special::{
    exec_function_with_self_return, find_and_exec_method_with_self, find_and_exec_method_with_self_owned,
    lookup_class_method_index, lookup_impl_method_index,
};

fn use_bare_module_fallback(receiver_in_env: bool, receiver_is_class: bool, receiver_is_enum: bool) -> bool {
    !receiver_in_env && !receiver_is_class && !receiver_is_enum
}

/// Main entry point for method call evaluation
#[allow(clippy::borrowed_box, clippy::too_many_arguments)] // reason: Box<dyn Trait> dispatch with ABI-locked entry; refactoring deferred
pub(crate) fn evaluate_method_call(
    receiver: &Box<Expr>,
    method: &str,
    args: &[Argument],
    env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    // Support module-style dot calls (lib.func()) by resolving directly to imported functions/classes.
    if let Expr::Identifier(module_name) = receiver.as_ref() {
        if method == "empty" {
            if let Ok(filter) = std::env::var("SIMPLE_INTERPRETER_CALL_TRACE") {
                if filter == "1" || filter == "all" || method.contains(&filter) {
                    eprintln!(
                        "[interp-call-route] route=method receiver={} name={} argc={} env={} class={}",
                        module_name,
                        method,
                        args.len(),
                        env.get(module_name).is_some(),
                        classes.contains_key(module_name)
                    );
                }
            }
        }
        // A `module_name` that isn't a local binding and isn't a class can
        // still be a genuine ENUM TYPE name (`EnumName.Variant(args)`) --
        // `env` here is the CURRENT (often function-local) environment, which
        // does not carry the module-level `Value::EnumType` binding that
        // `evaluate_module_impl`'s first pass inserts only into the
        // module-level `env` (see `interpreter/expr/literals.rs`'s
        // `Expr::Identifier` handling, which already falls back to
        // `enums`/`GLOBAL_ENUMS` for exactly this reason). Without this
        // check, `use_bare_module_fallback` mis-treats every enum-variant
        // constructor call made from inside a function/method body as a bare
        // global lookup on the VARIANT name alone, silently constructing an
        // unrelated global class/function that happens to share the
        // variant's bare name (e.g. `StmtKind.Expr(x)` inside a function
        // resolved to the unrelated `class Expr:` instead of the
        // `StmtKind::Expr` variant, because "Expr" is both a variant name
        // and a global struct name) instead of falling through to the
        // correct `Value::EnumType` construction path below. See bug doc
        // hir_stmt_expr_payload_extraction_nil_2026-07-17.md (Wall 2).
        let receiver_is_enum = enums.contains_key(module_name)
            || GLOBAL_ENUMS.with(|cell| cell.borrow().contains_key(module_name))
            || BLOCK_SCOPED_ENUMS.with(|cell| cell.borrow().contains_key(module_name));
        if use_bare_module_fallback(
            env.get(module_name).is_some(),
            classes.contains_key(module_name),
            receiver_is_enum,
        ) {
            if let Some(func) = functions.get(method).cloned() {
                return exec_function(&func, args, env, functions, classes, enums, impl_methods, None);
            }
            if classes.contains_key(method) {
                return instantiate_class(method, args, env, functions, classes, enums, impl_methods);
            }
        }

        // Builtin text static methods
        if module_name == "text" && method == "from_char_code" {
            let evaluated_args: Vec<Value> = args
                .iter()
                .map(|a| evaluate_expr(&a.value, env, functions, classes, enums, impl_methods))
                .collect::<Result<Vec<_>, _>>()?;
            let code = match evaluated_args.first() {
                Some(Value::Int(i)) => *i,
                _ => 0,
            };
            let ch = char::from_u32(code as u32).unwrap_or('\0');
            return Ok(Value::text(ch.to_string()));
        }
    }

    let recv_val = evaluate_expr(receiver, env, functions, classes, enums, impl_methods)?.deref_pointer();

    // Handle module (Dict) method calls - look up function in module and use its captured_env
    if let Value::Dict(module_dict) = &recv_val {
        if let Some(func_val) = module_dict.get(method) {
            if let Value::Function { def, captured_env, .. } = func_val {
                let mut captured_env_clone = Env::clone(captured_env);
                return exec_function_with_captured_env(
                    def,
                    args,
                    env,
                    &mut captured_env_clone,
                    functions,
                    classes,
                    enums,
                    impl_methods,
                );
            }
            if let Value::Constructor { class_name } = func_val {
                return instantiate_class(class_name, args, env, functions, classes, enums, impl_methods);
            }
        }
        // Handle typed dict objects (from ClassName.new()) - look up methods from impl/class
        if let Some(Value::Str(type_name)) = module_dict.get("__type__") {
            // Try impl_methods for this type
            if let Some(methods) = impl_methods.get(type_name.as_str()) {
                if let Some(func) = methods.iter().find(|m| m.name == method) {
                    // Build self_fields from the dict and pass via self_ctx so that args are
                    // evaluated in the CALLER's env (outer_env) before self is rebound.
                    // Previously this mutated outer_env with self= before calling exec_function,
                    // which caused me.field arg expressions to resolve against the callee's
                    // receiver rather than the caller's. (bug: self not found 2026-06-11)
                    let self_fields = Arc::new(
                        module_dict
                            .iter()
                            .map(|(k, v)| (k.clone(), v.clone()))
                            .collect::<HashMap<_, _>>(),
                    );
                    let type_name_str = type_name.as_str();
                    return super::exec_function(
                        func,
                        args,
                        env,
                        functions,
                        classes,
                        enums,
                        impl_methods,
                        Some((type_name_str, &self_fields)),
                    );
                }
            }
            // Try class methods
            if let Some(class_def) = classes.get(type_name.as_str()).cloned() {
                if let Some(func) = class_def.methods.iter().find(|m| m.name == method) {
                    // Same fix: build self_fields and pass via self_ctx instead of mutating outer_env.
                    let self_fields = Arc::new(
                        module_dict
                            .iter()
                            .map(|(k, v)| (k.clone(), v.clone()))
                            .collect::<HashMap<_, _>>(),
                    );
                    let type_name_str = type_name.as_str();
                    return super::exec_function(
                        func,
                        args,
                        env,
                        functions,
                        classes,
                        enums,
                        impl_methods,
                        Some((type_name_str, &self_fields)),
                    );
                }
            }
        }
    }

    // BDD assertion shortcut methods: to_equal, to_be, to_contain, etc.
    // These combine expect(val).to(matcher) into expect(val).to_equal(expected).
    // A passing matcher must not clear an earlier failure in the same `it`;
    // the example-level reset above is the only success-state reset point.
    use crate::value::MatcherValue;
    // A `.to_*()` matcher is being applied to the expect receiver, so a prior
    // bare-call "hollow expect" provisional failure no longer applies — the call
    // result IS being checked here. Clear it before the matcher arm records its
    // own result (the matcher still sets BDD_EXPECT_FAILED on mismatch).
    if matches!(
        method,
        "to_equal"
            | "to_be"
            | "to_contain"
            | "to_include"
            | "to_be_truthy"
            | "to_be_falsy"
            | "to_be_true"
            | "to_be_false"
            | "to_be_nil"
            | "to_be_none"
            | "to_be_greater_than"
            | "to_be_less_than"
            | "to_be_greater_than_or_equal"
            | "to_be_gte"
            | "to_be_less_than_or_equal"
            | "to_be_lte"
            | "to_start_with"
            | "to_end_with"
            | "to_not_equal"
            | "to_not_contain"
            | "to_not_include"
            | "to_not_be_nil"
            | "to"
            | "not_to"
            | "to_not"
    ) {
        use crate::interpreter::interpreter_call::{BDD_EXPECT_PROVISIONAL, BDD_MATCHER_COUNT, BDD_MATCHER_RAN};
        BDD_EXPECT_PROVISIONAL.with(|cell: &std::cell::RefCell<bool>| *cell.borrow_mut() = false);
        // Monotonic within an example: records that a matcher checked the expect
        // receiver, so a re-set provisional flag can't false-fail the example.
        BDD_MATCHER_RAN.with(|cell: &std::cell::RefCell<bool>| *cell.borrow_mut() = true);
        // Counted form, paired with BDD_EXPECT_NEEDS_MATCHER, so a vacuous
        // `expect(<non-bool>)` is caught even when a sibling expect in the same
        // example did chain a matcher. See bdd.rs for the contract.
        BDD_MATCHER_COUNT.with(|cell: &std::cell::RefCell<usize>| *cell.borrow_mut() += 1);
    }
    match method {
        "to_equal" | "to_be" => {
            let expected = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
            // Must use nullable-aware equality, not raw `==`: a receiver from a
            // `-> T?` function arrives as `Option::None`/`Option::Some(x)`, so raw
            // `==` made `to_equal(nil)` a FALSE FAILURE on a genuinely-nil value
            // and `to_equal(x)` a false failure on a genuinely-matching one.
            let matched = recv_val.nullable_eq(&expected);
            use crate::interpreter::interpreter_call::{BDD_EXPECT_FAILED, BDD_FAILURE_MSG};
            if !matched {
                BDD_EXPECT_FAILED.with(|cell: &std::cell::RefCell<bool>| *cell.borrow_mut() = true);
                let failure_msg = format!(
                    "expected {} to equal {}",
                    recv_val.to_display_string(),
                    expected.to_display_string()
                );
                BDD_FAILURE_MSG
                    .with(|cell: &std::cell::RefCell<Option<String>>| *cell.borrow_mut() = Some(failure_msg));
            }
            return Ok(Value::Bool(matched));
        }
        "to_contain" | "to_include" => {
            let needle = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
            let matched = match &recv_val {
                Value::Str(s) => {
                    if let Value::Str(n) = &needle {
                        s.contains(n.as_str())
                    } else {
                        false
                    }
                }
                Value::Array(arr) => arr.contains(&needle),
                _ => false,
            };
            use crate::interpreter::interpreter_call::{BDD_EXPECT_FAILED, BDD_FAILURE_MSG};
            if !matched {
                BDD_EXPECT_FAILED.with(|cell: &std::cell::RefCell<bool>| *cell.borrow_mut() = true);
                let failure_msg = format!(
                    "expected {} to contain {}",
                    recv_val.to_display_string(),
                    needle.to_display_string()
                );
                BDD_FAILURE_MSG
                    .with(|cell: &std::cell::RefCell<Option<String>>| *cell.borrow_mut() = Some(failure_msg));
            }
            return Ok(Value::Bool(matched));
        }
        "to_be_truthy" => {
            let matched = recv_val.truthy();
            use crate::interpreter::interpreter_call::{BDD_EXPECT_FAILED, BDD_FAILURE_MSG};
            if !matched {
                BDD_EXPECT_FAILED.with(|cell: &std::cell::RefCell<bool>| *cell.borrow_mut() = true);
                let failure_msg = format!("expected {} to be truthy", recv_val.to_display_string());
                BDD_FAILURE_MSG
                    .with(|cell: &std::cell::RefCell<Option<String>>| *cell.borrow_mut() = Some(failure_msg));
            }
            return Ok(Value::Bool(matched));
        }
        "to_be_falsy" => {
            let matched = !recv_val.truthy();
            use crate::interpreter::interpreter_call::{BDD_EXPECT_FAILED, BDD_FAILURE_MSG};
            if !matched {
                BDD_EXPECT_FAILED.with(|cell: &std::cell::RefCell<bool>| *cell.borrow_mut() = true);
                let failure_msg = format!("expected {} to be falsy", recv_val.to_display_string());
                BDD_FAILURE_MSG
                    .with(|cell: &std::cell::RefCell<Option<String>>| *cell.borrow_mut() = Some(failure_msg));
            }
            return Ok(Value::Bool(matched));
        }
        "to_be_true" => {
            // Strict equality (not just truthy) — mirrors
            // ExpectHelper.to_be_true in src/lib/nogc_sync_mut/spec.spl
            // (`self.value != true` fails), unlike `to_be_truthy` which
            // accepts any truthy value.
            let matched = recv_val == Value::Bool(true);
            use crate::interpreter::interpreter_call::{BDD_EXPECT_FAILED, BDD_FAILURE_MSG};
            if !matched {
                BDD_EXPECT_FAILED.with(|cell: &std::cell::RefCell<bool>| *cell.borrow_mut() = true);
                let failure_msg = format!("expected true, got {}", recv_val.to_display_string());
                BDD_FAILURE_MSG
                    .with(|cell: &std::cell::RefCell<Option<String>>| *cell.borrow_mut() = Some(failure_msg));
            }
            return Ok(Value::Bool(matched));
        }
        "to_be_false" => {
            // Strict equality (not just falsy) — mirrors
            // ExpectHelper.to_be_false in src/lib/nogc_sync_mut/spec.spl
            // (`self.value != false` fails), unlike `to_be_falsy` which
            // accepts any falsy value.
            let matched = recv_val == Value::Bool(false);
            use crate::interpreter::interpreter_call::{BDD_EXPECT_FAILED, BDD_FAILURE_MSG};
            if !matched {
                BDD_EXPECT_FAILED.with(|cell: &std::cell::RefCell<bool>| *cell.borrow_mut() = true);
                let failure_msg = format!("expected false, got {}", recv_val.to_display_string());
                BDD_FAILURE_MSG
                    .with(|cell: &std::cell::RefCell<Option<String>>| *cell.borrow_mut() = Some(failure_msg));
            }
            return Ok(Value::Bool(matched));
        }
        "to_be_nil" | "to_be_none" => {
            // Treat Option::None as nil-like (matches `== nil` semantics via
            // Value::is_nil_like), so `expect(none_option).to_be_nil()` /
            // `.to_be_none()` pass instead of failing with "expected Option::None
            // to be nil".
            let matched = recv_val.is_nil_like();
            use crate::interpreter::interpreter_call::{BDD_EXPECT_FAILED, BDD_FAILURE_MSG};
            if !matched {
                BDD_EXPECT_FAILED.with(|cell: &std::cell::RefCell<bool>| *cell.borrow_mut() = true);
                let failure_msg = format!("expected {} to be nil", recv_val.to_display_string());
                BDD_FAILURE_MSG
                    .with(|cell: &std::cell::RefCell<Option<String>>| *cell.borrow_mut() = Some(failure_msg));
            }
            return Ok(Value::Bool(matched));
        }
        "to_be_greater_than" => {
            let expected = eval_arg(args, 0, Value::Int(0), env, functions, classes, enums, impl_methods)?;
            let matched = numeric_ordering(&recv_val, &expected).is_some_and(|ordering| ordering.is_gt());
            use crate::interpreter::interpreter_call::{BDD_EXPECT_FAILED, BDD_FAILURE_MSG};
            if !matched {
                BDD_EXPECT_FAILED.with(|cell: &std::cell::RefCell<bool>| *cell.borrow_mut() = true);
                let failure_msg = format!(
                    "expected {} to be greater than {}",
                    recv_val.to_display_string(),
                    expected.to_display_string()
                );
                BDD_FAILURE_MSG
                    .with(|cell: &std::cell::RefCell<Option<String>>| *cell.borrow_mut() = Some(failure_msg));
            }
            return Ok(Value::Bool(matched));
        }
        "to_be_less_than" => {
            let expected = eval_arg(args, 0, Value::Int(0), env, functions, classes, enums, impl_methods)?;
            let matched = numeric_ordering(&recv_val, &expected).is_some_and(|ordering| ordering.is_lt());
            use crate::interpreter::interpreter_call::{BDD_EXPECT_FAILED, BDD_FAILURE_MSG};
            if !matched {
                BDD_EXPECT_FAILED.with(|cell: &std::cell::RefCell<bool>| *cell.borrow_mut() = true);
                let failure_msg = format!(
                    "expected {} to be less than {}",
                    recv_val.to_display_string(),
                    expected.to_display_string()
                );
                BDD_FAILURE_MSG
                    .with(|cell: &std::cell::RefCell<Option<String>>| *cell.borrow_mut() = Some(failure_msg));
            }
            return Ok(Value::Bool(matched));
        }
        "to_be_greater_than_or_equal" | "to_be_gte" => {
            let expected = eval_arg(args, 0, Value::Int(0), env, functions, classes, enums, impl_methods)?;
            let matched =
                numeric_ordering(&recv_val, &expected).is_some_and(|ordering| ordering.is_gt() || ordering.is_eq());
            use crate::interpreter::interpreter_call::{BDD_EXPECT_FAILED, BDD_FAILURE_MSG};
            if !matched {
                BDD_EXPECT_FAILED.with(|cell: &std::cell::RefCell<bool>| *cell.borrow_mut() = true);
                let failure_msg = format!(
                    "expected {} to be greater than or equal to {}",
                    recv_val.to_display_string(),
                    expected.to_display_string()
                );
                BDD_FAILURE_MSG
                    .with(|cell: &std::cell::RefCell<Option<String>>| *cell.borrow_mut() = Some(failure_msg));
            }
            return Ok(Value::Bool(matched));
        }
        "to_be_less_than_or_equal" | "to_be_lte" => {
            let expected = eval_arg(args, 0, Value::Int(0), env, functions, classes, enums, impl_methods)?;
            let matched =
                numeric_ordering(&recv_val, &expected).is_some_and(|ordering| ordering.is_lt() || ordering.is_eq());
            use crate::interpreter::interpreter_call::{BDD_EXPECT_FAILED, BDD_FAILURE_MSG};
            if !matched {
                BDD_EXPECT_FAILED.with(|cell: &std::cell::RefCell<bool>| *cell.borrow_mut() = true);
                let failure_msg = format!(
                    "expected {} to be less than or equal to {}",
                    recv_val.to_display_string(),
                    expected.to_display_string()
                );
                BDD_FAILURE_MSG
                    .with(|cell: &std::cell::RefCell<Option<String>>| *cell.borrow_mut() = Some(failure_msg));
            }
            return Ok(Value::Bool(matched));
        }
        "to_start_with" => {
            let prefix = eval_arg(
                args,
                0,
                Value::text(String::new()),
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )?;
            let matched = match (&recv_val, &prefix) {
                (Value::Str(s), Value::Str(p)) => s.starts_with(p.as_str()),
                _ => false,
            };
            use crate::interpreter::interpreter_call::{BDD_EXPECT_FAILED, BDD_FAILURE_MSG};
            if !matched {
                BDD_EXPECT_FAILED.with(|cell: &std::cell::RefCell<bool>| *cell.borrow_mut() = true);
                let failure_msg = format!(
                    "expected {} to start with {}",
                    recv_val.to_display_string(),
                    prefix.to_display_string()
                );
                BDD_FAILURE_MSG
                    .with(|cell: &std::cell::RefCell<Option<String>>| *cell.borrow_mut() = Some(failure_msg));
            }
            return Ok(Value::Bool(matched));
        }
        "to_end_with" => {
            let suffix = eval_arg(
                args,
                0,
                Value::text(String::new()),
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )?;
            let matched = match (&recv_val, &suffix) {
                (Value::Str(s), Value::Str(p)) => s.ends_with(p.as_str()),
                _ => false,
            };
            use crate::interpreter::interpreter_call::{BDD_EXPECT_FAILED, BDD_FAILURE_MSG};
            if !matched {
                BDD_EXPECT_FAILED.with(|cell: &std::cell::RefCell<bool>| *cell.borrow_mut() = true);
                let failure_msg = format!(
                    "expected {} to end with {}",
                    recv_val.to_display_string(),
                    suffix.to_display_string()
                );
                BDD_FAILURE_MSG
                    .with(|cell: &std::cell::RefCell<Option<String>>| *cell.borrow_mut() = Some(failure_msg));
            }
            return Ok(Value::Bool(matched));
        }
        "to_not_equal" => {
            let expected = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
            // Nullable-aware, per `to_equal` above. With raw `!=` this was the
            // dangerous direction: `to_not_equal(nil)` on a genuinely-nil value
            // and `to_not_equal(x)` on a genuinely-equal one both FALSE-PASSED.
            let matched = !recv_val.nullable_eq(&expected);
            use crate::interpreter::interpreter_call::{BDD_EXPECT_FAILED, BDD_FAILURE_MSG};
            if !matched {
                BDD_EXPECT_FAILED.with(|cell: &std::cell::RefCell<bool>| *cell.borrow_mut() = true);
                let failure_msg = format!(
                    "expected {} to not equal {}",
                    recv_val.to_display_string(),
                    expected.to_display_string()
                );
                BDD_FAILURE_MSG
                    .with(|cell: &std::cell::RefCell<Option<String>>| *cell.borrow_mut() = Some(failure_msg));
            }
            return Ok(Value::Bool(matched));
        }
        "to_not_contain" | "to_not_include" => {
            let needle = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
            let contains = match &recv_val {
                Value::Str(s) => {
                    if let Value::Str(n) = &needle {
                        s.contains(n.as_str())
                    } else {
                        false
                    }
                }
                Value::Array(arr) => arr.contains(&needle),
                _ => false,
            };
            let matched = !contains;
            use crate::interpreter::interpreter_call::{BDD_EXPECT_FAILED, BDD_FAILURE_MSG};
            if !matched {
                BDD_EXPECT_FAILED.with(|cell: &std::cell::RefCell<bool>| *cell.borrow_mut() = true);
                let failure_msg = format!(
                    "expected {} to not contain {}",
                    recv_val.to_display_string(),
                    needle.to_display_string()
                );
                BDD_FAILURE_MSG
                    .with(|cell: &std::cell::RefCell<Option<String>>| *cell.borrow_mut() = Some(failure_msg));
            }
            return Ok(Value::Bool(matched));
        }
        "to_not_be_nil" => {
            // Symmetric with to_be_nil: Option::None counts as nil-like, so
            // to_not_be_nil(None) correctly fails.
            let matched = !recv_val.is_nil_like();
            use crate::interpreter::interpreter_call::{BDD_EXPECT_FAILED, BDD_FAILURE_MSG};
            if !matched {
                BDD_EXPECT_FAILED.with(|cell: &std::cell::RefCell<bool>| *cell.borrow_mut() = true);
                BDD_FAILURE_MSG.with(|cell: &std::cell::RefCell<Option<String>>| {
                    *cell.borrow_mut() = Some("expected value to not be nil, got nil".to_string())
                });
            }
            return Ok(Value::Bool(matched));
        }
        // BDD assertion methods: to(matcher) and not_to(matcher)
        // These work on any value type and are used with matchers like eq(5), gt(3), etc.
        "to" | "not_to" | "to_not" => {
            let matcher = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
            let matched = match &matcher {
                Value::Matcher(m) => m.matches(&recv_val),
                // If the argument isn't a Matcher, treat it as an equality check
                other => recv_val == *other,
            };
            let is_negated = method == "not_to" || method == "to_not";
            let passed = if is_negated { !matched } else { matched };

            // Report to BDD framework
            use crate::interpreter::interpreter_call::{BDD_EXPECT_FAILED, BDD_FAILURE_MSG};
            if !passed {
                BDD_EXPECT_FAILED.with(|cell: &std::cell::RefCell<bool>| *cell.borrow_mut() = true);
                let failure_msg = format!(
                    "expected {:?} {} {:?}",
                    recv_val,
                    if is_negated { "not to match" } else { "to match" },
                    matcher
                );
                BDD_FAILURE_MSG
                    .with(|cell: &std::cell::RefCell<Option<String>>| *cell.borrow_mut() = Some(failure_msg));
            }

            return Ok(Value::Bool(passed));
        }
        _ => {}
    }

    // Dispatch to type-specific handlers
    match &recv_val {
        Value::Int(n) => {
            if let Some(result) =
                primitives::handle_int_methods(*n, method, args, env, functions, classes, enums, impl_methods)?
            {
                return Ok(result);
            }
        }
        // Keep unsigned receivers on an unsigned path for methods whose
        // observable result depends on the sign bit (for example `to_text()`
        // on `0xCAFEBABEDEADBEEFu64`). Fall back to the signed helper for the
        // legacy int API after preserving the common unsigned cases.
        Value::UInt { value, width } => {
            match method {
                "abs" => {
                    return Ok(Value::UInt {
                        value: *value,
                        width: *width,
                    })
                }
                "sign" | "signum" => {
                    return Ok(Value::UInt {
                        value: if *value == 0 { 0 } else { 1 },
                        width: *width,
                    })
                }
                "is_positive" => return Ok(Value::Bool(*value > 0)),
                "is_negative" => return Ok(Value::Bool(false)),
                "is_zero" => return Ok(Value::Bool(*value == 0)),
                "is_even" => return Ok(Value::Bool(*value % 2 == 0)),
                "is_odd" => return Ok(Value::Bool(*value % 2 != 0)),
                "to_float" | "to_f64" => return Ok(Value::Float(*value as f64)),
                "to_f32" => return Ok(Value::Float32(*value as f32)),
                "to_u8" => {
                    return Ok(Value::UInt {
                        value: (*value as u8) as u64,
                        width: 8,
                    })
                }
                "to_u16" => {
                    return Ok(Value::UInt {
                        value: (*value as u16) as u64,
                        width: 16,
                    })
                }
                "to_u32" => {
                    return Ok(Value::UInt {
                        value: (*value as u32) as u64,
                        width: 32,
                    })
                }
                "to_u64" => {
                    return Ok(Value::UInt {
                        value: *value,
                        width: 64,
                    })
                }
                "to_i8" => return Ok(Value::Int(*value as u8 as i8 as i64)),
                "to_i16" => return Ok(Value::Int(*value as u16 as i16 as i64)),
                "to_i32" => return Ok(Value::Int(*value as u32 as i32 as i64)),
                "to_i64" => return Ok(Value::Int(*value as i64)),
                "to_string" | "to_text" => return Ok(Value::text(value.to_string())),
                "bit_count" | "count_ones" => return Ok(Value::Int(value.count_ones() as i64)),
                "leading_zeros" => return Ok(Value::Int(value.leading_zeros() as i64)),
                "trailing_zeros" => return Ok(Value::Int(value.trailing_zeros() as i64)),
                "to_hex" => return Ok(Value::text(format!("{:x}", value))),
                "to_bin" => return Ok(Value::text(format!("{:b}", value))),
                "to_oct" => return Ok(Value::text(format!("{:o}", value))),
                _ => {}
            }
            if let Some(result) = primitives::handle_int_methods(
                *value as i64,
                method,
                args,
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )? {
                return Ok(result);
            }
        }
        Value::Float(f) => {
            if let Some(result) =
                primitives::handle_float_methods(*f, method, args, env, functions, classes, enums, impl_methods)?
            {
                return Ok(result);
            }
        }
        // Float32 dispatch: f32-precision-preserving methods. For unary methods
        // like abs/floor/ceil/round, f32 -> f64 -> f32 is bit-exact, so we
        // delegate to handle_float_methods and re-narrow on the way out for
        // float-typed results. `to_f32` and `to_f64` are handled directly to
        // emit the right Value variant.
        Value::Float32(f) => {
            // Direct cases that need explicit Float32/Float boundaries.
            match method {
                "to_f32" => return Ok(Value::Float32(*f)),
                "to_f64" | "to_float" => return Ok(Value::Float(*f as f64)),
                "to_string" | "to_text" => return Ok(Value::text(format_f32_display(*f))),
                _ => {}
            }
            // Delegate to handle_float_methods for arithmetic helpers; if it
            // returns a Float result, re-narrow to Float32 to preserve the
            // single-precision tag.
            if let Some(result) =
                primitives::handle_float_methods(*f as f64, method, args, env, functions, classes, enums, impl_methods)?
            {
                let narrowed = match result {
                    Value::Float(v) => Value::Float32(v as f32),
                    other => other,
                };
                return Ok(narrowed);
            }
        }
        Value::Bool(b) => {
            if let Some(result) =
                primitives::handle_bool_methods(*b, method, args, env, functions, classes, enums, impl_methods)?
            {
                return Ok(result);
            }
        }
        Value::Unit { value, suffix, family } => {
            if let Some(result) = special::handle_unit_methods(
                value,
                suffix,
                family,
                method,
                args,
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )? {
                return Ok(result);
            }
        }
        Value::Array(arr) => {
            if let Some(result) =
                collections::handle_array_methods(arr, method, args, env, functions, classes, enums, impl_methods)?
            {
                return Ok(result);
            }
        }
        Value::ByteArray(bytes) => {
            if let Some(result) = collections::handle_byte_array_methods(
                bytes,
                false,
                method,
                args,
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )? {
                return Ok(result);
            }
        }
        Value::FrozenArray(arc_arr) => {
            if let Some(result) = collections::handle_frozen_array_methods(
                arc_arr,
                method,
                args,
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )? {
                return Ok(result);
            }
        }
        Value::FrozenByteArray(bytes) => {
            if let Some(result) = collections::handle_byte_array_methods(
                bytes,
                true,
                method,
                args,
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )? {
                return Ok(result);
            }
        }
        Value::FixedSizeArray { size, data } => {
            if let Some(result) = collections::handle_fixed_size_array_methods(
                *size,
                data,
                method,
                args,
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )? {
                return Ok(result);
            }
        }
        Value::Tuple(tup) => {
            if let Some(result) =
                collections::handle_tuple_methods(tup, method, args, env, functions, classes, enums, impl_methods)?
            {
                return Ok(result);
            }
        }
        Value::Dict(map) => {
            if let Some(result) =
                collections::handle_dict_methods(map, method, args, env, functions, classes, enums, impl_methods)?
            {
                return Ok(result);
            }
        }
        Value::FrozenDict(arc_map) => {
            if let Some(result) = collections::handle_frozen_dict_methods(
                arc_map,
                method,
                args,
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )? {
                return Ok(result);
            }
        }
        Value::Str(_) => {
            // String methods are included from a separate file
            include!("string.rs");
        }
        Value::StrBytes(bytes) => {
            // `StrBytes` holds raw bytes that are NOT valid UTF-8 (a
            // mid-codepoint slice fragment; see `Value::text_from_bytes`).
            // It had NO method-dispatch arm at all, so every method call —
            // even `.len()` — fell through to the generic "method not
            // found" error, which rendered the receiver via
            // `to_display_string()`'s lossy path and produced the
            // self-contradictory `method 'len' not found on type 'str'`.
            //
            // Byte-transparent fast paths first: these methods' *results*
            // depend on the exact byte count, so they must read `bytes`
            // directly rather than through a lossy stand-in (U+FFFD
            // substitution changes the byte length).
            match method {
                "len" | "length" => return Ok(Value::Int(bytes.len() as i64)),
                "is_empty" => return Ok(Value::Bool(bytes.is_empty())),
                "bytes" => {
                    let out: Vec<Value> = bytes.iter().map(|b| Value::Int(*b as i64)).collect();
                    return Ok(Value::array(out));
                }
                _ => {}
            }
            // Every other string method: StrBytes fragments exist to stay
            // byte-transparent through indexing/concatenation/join (see
            // `Value::text_from_bytes` / `text_bytes_view`); once a caller
            // asks for a string-shaped operation beyond raw length/bytes,
            // rendering lossily to `Str` and reusing the shared
            // string-method table is the SAME display-boundary rule already
            // applied by `to_display_string()` and the FFI value bridge
            // (`value_bridge.rs`'s `Value::StrBytes(bs) =>
            // BridgeValue::string(&String::from_utf8_lossy(bs)...)`), not a
            // new fidelity regression.
            let recv_val = Value::text(String::from_utf8_lossy(bytes).into_owned());
            include!("string.rs");
        }
        Value::Enum {
            enum_name,
            variant,
            payload,
        } => {
            // Try Option methods
            if let Some(result) = special::handle_option_methods(
                &recv_val,
                enum_name,
                variant,
                payload,
                method,
                args,
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )? {
                return Ok(result);
            }
            // Try Result methods
            if let Some(result) = special::handle_result_methods(
                &recv_val,
                enum_name,
                variant,
                payload,
                method,
                args,
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )? {
                return Ok(result);
            }

            // User-defined methods on enums via impl blocks
            if let Some(methods) = impl_methods.get(enum_name) {
                for m in methods {
                    if m.name == method {
                        // For enum methods, we pass self as a special context
                        // Create a fields map with just "self" for the enum value
                        let mut enum_fields = HashMap::new();
                        enum_fields.insert("self".to_string(), recv_val.clone());
                        let enum_fields = Arc::new(enum_fields);
                        let result = exec_function(
                            m,
                            args,
                            env,
                            functions,
                            classes,
                            enums,
                            impl_methods,
                            Some((enum_name, &enum_fields)),
                        )?;
                        return Ok(result);
                    }
                }
            }

            // Methods defined directly in the enum body (or merged from impl blocks).
            // Try the local `enums` map first, then fall back to GLOBAL_ENUMS so
            // that methods on cross-module enums stored as struct fields are found.
            let enum_def_opt = enums
                .get(enum_name)
                .cloned()
                .or_else(|| GLOBAL_ENUMS.with(|cell| cell.borrow().get(enum_name).cloned()));
            if let Some(enum_def) = enum_def_opt {
                for m in &enum_def.methods {
                    if m.name == method {
                        // For enum methods, we pass self as a special context
                        let mut enum_fields = HashMap::new();
                        enum_fields.insert("self".to_string(), recv_val.clone());
                        let enum_fields = Arc::new(enum_fields);
                        return exec_function(
                            m,
                            args,
                            env,
                            functions,
                            classes,
                            enums,
                            impl_methods,
                            Some((enum_name, &enum_fields)),
                        );
                    }
                }
            }

            // Some(x) member-call forwarding. Since 60fd804c, `-> T?` functions
            // Some-wrap their plain returns; such a value can then be funneled
            // into a non-Optional context the lib treats as a bare value — e.g.
            // an element of a `[WidgetNode]` built from `get_widget(...)` calls.
            // After every real Option/Result/enum method has missed, dispatch a
            // *user* method to the inner value so `Some(node).is_visible()` works
            // as `node.is_visible()` did before wrapping. `None` is left to the
            // error below, so nil-dereferences stay caught.
            if enum_name == "Option" && variant == "Some" {
                if let Some(inner) = payload {
                    let inner_val = (**inner).clone();
                    const FWD_RECV: &str = "__option_some_fwd_receiver__";
                    let prev = env.insert(FWD_RECV.to_string(), inner_val);
                    let fwd_expr: Box<Expr> = Box::new(Expr::Identifier(FWD_RECV.to_string()));
                    let forwarded =
                        evaluate_method_call(&fwd_expr, method, args, env, functions, classes, enums, impl_methods);
                    match prev {
                        Some(v) => {
                            env.insert(FWD_RECV.to_string(), v);
                        }
                        None => {
                            env.remove(FWD_RECV);
                        }
                    }
                    return forwarded;
                }
            }
        }
        // EnumType method call = variant constructor call
        // EnumName.VariantName(args) -> create enum with payload
        Value::EnumType { enum_name } => {
            // Check module-local, block-scoped, and imported enums.
            let enum_def = enums
                .get(enum_name)
                .cloned()
                .or_else(|| BLOCK_SCOPED_ENUMS.with(|cell| cell.borrow().get(enum_name).cloned()))
                .or_else(|| GLOBAL_ENUMS.with(|cell| cell.borrow().get(enum_name).cloned()));
            if let Some(enum_def) = enum_def {
                // Check if the method name is a variant name
                let variant_opt = enum_def.variants.iter().find(|v| v.name == method);
                if let Some(variant) = variant_opt {
                    // Construct enum variant with payload
                    let has_fields = variant.fields.as_ref().is_some_and(|f| !f.is_empty());
                    if !has_fields && args.is_empty() {
                        // Unit variant
                        return Ok(Value::Enum {
                            enum_name: enum_name.clone(),
                            variant: method.to_string(),
                            payload: None,
                        });
                    } else {
                        // Variant with payload
                        let payload = if args.is_empty() {
                            None
                        } else if args.len() == 1 {
                            let val = evaluate_expr(&args[0].value, env, functions, classes, enums, impl_methods)?;
                            Some(Box::new(val))
                        } else {
                            // Multiple args - wrap in tuple
                            let vals: Result<Vec<Value>, _> = args
                                .iter()
                                .map(|a| evaluate_expr(&a.value, env, functions, classes, enums, impl_methods))
                                .collect();
                            Some(Box::new(Value::Tuple(vals?)))
                        };
                        return Ok(Value::Enum {
                            enum_name: enum_name.clone(),
                            variant: method.to_string(),
                            payload,
                        });
                    }
                }

                // Check if it's a static method on the enum (declared inline in
                // the enum body, e.g. `enum E: ... static fn make() -> E: ...`).
                for m in &enum_def.methods {
                    if m.name == method && m.params.first().is_none_or(|p| p.name != "self") {
                        return exec_function(m, args, env, functions, classes, enums, impl_methods, None);
                    }
                }

                // Also check static methods declared via a separate `impl
                // EnumName:` block. These are registered into `impl_methods`
                // (module-local) / `GLOBAL_IMPL_METHODS` (cross-module
                // fallback) by evaluate_module_impl exactly like enum-body
                // methods are registered into `enum_def.methods` above --
                // without this check, a same-file `impl Enum:` static was
                // never found because the only enum-callee dispatch path that
                // consults impl_methods is the imported-module Dict-export
                // path (`Value::Dict` receiver in this same function), which
                // an entry-file enum never goes through since it has no
                // `use` statement rebinding its env entry away from
                // `Value::EnumType`. See bug doc
                // enum_impl_static_fn_scoping_2026-07-29.md.
                let impl_static = impl_methods
                    .get(enum_name.as_str())
                    .and_then(|methods| methods.iter().find(|m| m.name == method).cloned())
                    .or_else(|| {
                        GLOBAL_IMPL_METHODS.with(|cell| {
                            cell.borrow()
                                .get(enum_name.as_str())
                                .and_then(|methods| methods.iter().find(|m| m.name == method).cloned())
                        })
                    });
                if let Some(m) = impl_static {
                    if m.params.first().is_none_or(|p| p.name != "self") {
                        return exec_function(&m, args, env, functions, classes, enums, impl_methods, None);
                    }
                }

                return Err(crate::error::factory::unknown_enum_variant_or_method(method, enum_name));
            } else {
                // E1015 - Unknown Enum
                let available_enums: Vec<&str> = enums.keys().map(|s| s.as_str()).collect();
                let suggestion = if !available_enums.is_empty() {
                    typo::suggest_name(enum_name, available_enums.clone())
                } else {
                    None
                };

                let mut ctx = ErrorContext::new()
                    .with_code(codes::UNKNOWN_ENUM)
                    .with_help("check that the enum is defined or imported in this scope");

                if let Some(best_match) = suggestion {
                    ctx = ctx.with_help(format!("did you mean `{}`?", best_match));
                }

                return Err(CompileError::semantic_with_context(
                    format!("enum `{}` not found in this scope", enum_name),
                    ctx,
                ));
            }
        }
        Value::TraitObject { trait_name, inner } => {
            if let Some(result) = special::handle_trait_object_methods(
                trait_name,
                inner,
                method,
                args,
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )? {
                return Ok(result);
            } else {
                // E1013 - Unknown Method (for dyn trait)
                let ctx = ErrorContext::new()
                    .with_code(codes::UNKNOWN_METHOD)
                    .with_help("check that the method is defined in the trait");

                return Err(CompileError::semantic_with_context(
                    format!("method `{}` not found on type `dyn {}`", method, trait_name),
                    ctx,
                ));
            }
        }
        Value::Object { class, fields } => {
            // Try to find and execute the method
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
                return Ok(result);
            }
            // Check if the method name corresponds to a callable field (Lambda/Function)
            // This allows patterns like: self.callback(arg) where callback is a lambda field
            if let Some(field_value) = fields.get(method) {
                match field_value {
                    Value::Lambda {
                        params,
                        body,
                        env: captured_env,
                    } => {
                        // Call the lambda stored in the field
                        let mut arg_vals = Vec::new();
                        for arg in args {
                            arg_vals.push(evaluate_expr(&arg.value, env, functions, classes, enums, impl_methods)?);
                        }
                        // Create local env from captured env and bind params
                        let mut local_env = Env::clone(captured_env);
                        for (i, param) in params.iter().enumerate() {
                            if let Some(val) = arg_vals.get(i) {
                                local_env.insert(param.clone(), val.clone());
                            }
                        }
                        // Evaluate the body expression
                        let result =
                            evaluate_expr(body.as_ref(), &mut local_env, functions, classes, enums, impl_methods)?;
                        return Ok(result);
                    }
                    Value::Function { def, captured_env, .. } => {
                        // Call the function stored in the field
                        return exec_function_with_captured_env(
                            def,
                            args,
                            env,
                            &mut Env::clone(captured_env),
                            functions,
                            classes,
                            enums,
                            impl_methods,
                        );
                    }
                    // Any OTHER callable field shape (block closure, native
                    // function, constructor, or an object implementing the
                    // `__call__` protocol) routes through the single place that
                    // knows which `Value` variants are invocable, so
                    // `obj.handler(x)` agrees with `(obj.handler)(x)`.
                    other => {
                        let candidate = other.clone();
                        if matches!(
                            candidate,
                            Value::BlockClosure { .. }
                                | Value::NativeFunction(_)
                                | Value::Constructor { .. }
                                | Value::Object { .. }
                        ) {
                            if let Some(result) = crate::interpreter::interpreter_call::call_value_as_callable(
                                candidate,
                                args,
                                env,
                                functions,
                                classes,
                                enums,
                                impl_methods,
                            )? {
                                return Ok(result);
                            }
                        }
                    }
                }
            }
            // Try method_missing hook
            if let Some(result) = try_method_missing(
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
                return Ok(result);
            }
            if let Some(result) =
                try_bare_some_option_method(&recv_val, method, args, env, functions, classes, enums, impl_methods)?
            {
                return Ok(result);
            }
            // Collect available methods for typo suggestion
            let mut available_methods: Vec<&str> = Vec::new();
            if let Some(methods) = impl_methods.get(class) {
                available_methods.extend(methods.iter().map(|m| m.name.as_str()));
            }
            // Add built-in methods for common types
            available_methods.extend(["new", "to_string", "clone", "equals"].iter().copied());
            bail_unknown_method!(method, class, available_methods);
        }
        Value::Future(future) => {
            if let Some(result) = special::handle_future_methods(future, method)? {
                return Ok(result);
            } else {
                let available = ["join", "await", "get", "is_ready"];
                bail_unknown_method!(method, "Future", available);
            }
        }
        Value::Channel(channel) => {
            if let Some(result) =
                special::handle_channel_methods(channel, method, args, env, functions, classes, enums, impl_methods)?
            {
                return Ok(result);
            } else {
                let available = ["send", "recv", "try_recv"];
                bail_unknown_method!(method, "Channel", available);
            }
        }
        Value::ThreadPool(pool) => {
            if let Some(result) =
                special::handle_threadpool_methods(pool, method, args, env, functions, classes, enums, impl_methods)?
            {
                return Ok(result);
            } else {
                let available = ["submit"];
                bail_unknown_method!(method, "ThreadPool", available);
            }
        }
        Value::Generator(gen) => match method {
            "next" => {
                return Ok(gen.next().unwrap_or(Value::Nil));
            }
            "is_done" => {
                return Ok(Value::Bool(gen.is_done()));
            }
            "collect" => {
                return Ok(Value::Array(Arc::new(gen.collect_remaining())));
            }
            _ => {
                return Err(CompileError::semantic(format!(
                    "method '{}' not found on generator",
                    method
                )));
            }
        },
        Value::Constructor { class_name } => {
            if let Some(result) = special::handle_constructor_methods(
                class_name,
                method,
                args,
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )? {
                return Ok(result);
            } else {
                return Err(crate::error::factory::class_not_found(class_name));
            }
        }
        Value::Mock(mock) => {
            if let Some(result) =
                special::handle_mock_methods(mock, method, args, env, functions, classes, enums, impl_methods)?
            {
                return Ok(result);
            }
            // Mock methods handler handles all cases including fallback
            unreachable!("Mock methods handler should have handled all cases");
        }
        Value::Nil => {
            // Treat nil as Option::None for Option-like methods
            match method {
                "map" | "and_then" | "flat_map" => {
                    // map/and_then on None returns None
                    return Ok(Value::Nil);
                }
                "or_else" => {
                    // or_else on None calls the closure
                    let func = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
                    if let Value::Lambda {
                        params,
                        body,
                        env: captured,
                    } = func
                    {
                        let mut local_env = Env::clone(&captured);
                        // No args to bind for or_else
                        return evaluate_expr(&body, &mut local_env, functions, classes, enums, impl_methods);
                    }
                    return Ok(Value::Nil);
                }
                "unwrap" => {
                    let ctx = ErrorContext::new()
                        .with_code(codes::INVALID_OPERATION)
                        .with_help("use unwrap_or(default) or check with is_some() first");
                    return Err(CompileError::semantic_with_context(
                        "called unwrap() on None/nil value".to_string(),
                        ctx,
                    ));
                }
                "unwrap_or" => {
                    // Return the default value
                    return eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods);
                }
                "unwrap_or_else" => {
                    // Call the closure and return its result
                    let func = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
                    if let Value::Lambda {
                        params,
                        body,
                        env: captured,
                    } = func
                    {
                        let mut local_env = Env::clone(&captured);
                        return evaluate_expr(&body, &mut local_env, functions, classes, enums, impl_methods);
                    }
                    return Ok(Value::Nil);
                }
                "is_some" | "is_present" => return Ok(Value::Bool(false)),
                "is_none" | "is_nil" | "is_null" => return Ok(Value::Bool(true)),
                "ok_or" => {
                    // Convert None to Err(default)
                    let err_val = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
                    return Ok(Value::err(err_val));
                }
                "expect" => {
                    let msg = eval_arg(
                        args,
                        0,
                        Value::text("expected Some value".to_string()),
                        env,
                        functions,
                        classes,
                        enums,
                        impl_methods,
                    )?;
                    let ctx = ErrorContext::new().with_code(codes::INVALID_OPERATION);
                    return Err(CompileError::semantic_with_context(
                        format!("expect() failed: {}", msg.to_display_string()),
                        ctx,
                    ));
                }
                _ => {} // Fall through to default error handling
            }
        }
        _ => {}
    }

    // Trait impl dispatch fallback for built-in types.
    // When a method isn't found by the type-specific handler above, check TRAIT_IMPLS
    // for user-defined trait implementations on built-in types (e.g., `impl MyTrait for text:`).
    {
        // Map Value type to the possible type names used in `impl Trait for TypeName:`
        let type_names: &[&str] = match &recv_val {
            Value::Str(_) | Value::StrBytes(_) => &["text", "str", "String"],
            Value::Int(_) => &["i64", "i32", "int"],
            Value::Float(_) => &["f64", "float"],
            Value::Float32(_) => &["f32", "float"],
            Value::Bool(_) => &["bool"],
            Value::Array(_)
            | Value::ByteArray(_)
            | Value::FrozenArray(_)
            | Value::FrozenByteArray(_)
            | Value::FixedSizeArray { .. } => &["array", "Array"],
            Value::Dict(_) | Value::FrozenDict(_) => &["dict", "Dict"],
            Value::Tuple(_) => &["tuple", "Tuple"],
            _ => &[],
        };

        if !type_names.is_empty() {
            // Search TRAIT_IMPLS for a method matching this type
            let trait_method: Option<Arc<FunctionDef>> = TRAIT_IMPLS.with(|cell| {
                let trait_impls = cell.borrow();
                for type_alias in type_names {
                    for ((_trait_name, impl_type), methods) in trait_impls.iter() {
                        if impl_type == type_alias {
                            if let Some(func) = methods.iter().find(|m| m.name == method) {
                                return Some(func.clone());
                            }
                        }
                    }
                }
                None
            });

            if let Some(func) = trait_method {
                // For built-in types, set self to the value directly (like enum methods)
                let mut self_fields = HashMap::new();
                self_fields.insert("self".to_string(), recv_val.clone());
                let self_fields = Arc::new(self_fields);
                let type_name = type_names[0];
                return exec_function(
                    &func,
                    args,
                    env,
                    functions,
                    classes,
                    enums,
                    impl_methods,
                    Some((type_name, &self_fields)),
                );
            }

            // Also check blanket impls for built-in types
            let blanket_method: Option<Arc<FunctionDef>> = BLANKET_IMPL_METHODS.with(|cell| {
                let blanket_impls = cell.borrow();
                for (_trait_name, methods) in blanket_impls.iter() {
                    if let Some(func) = methods.iter().find(|m| m.name == method) {
                        return Some(func.clone());
                    }
                }
                None
            });

            if let Some(func) = blanket_method {
                let mut self_fields = HashMap::new();
                self_fields.insert("self".to_string(), recv_val.clone());
                let self_fields = Arc::new(self_fields);
                let type_name = type_names[0];
                return exec_function(
                    &func,
                    args,
                    env,
                    functions,
                    classes,
                    enums,
                    impl_methods,
                    Some((type_name, &self_fields)),
                );
            }
        }
    }

    // UFCS Fallback: Try to find a free function with the method name
    // This allows both len(x) and x.len() syntax to work
    if let Some(func) = functions.get(method).cloned() {
        // Evaluate all arguments to values
        let mut arg_values = vec![recv_val.clone()]; // Receiver becomes first argument
        for arg in args {
            let val = evaluate_expr(&arg.value, env, functions, classes, enums, impl_methods)?;
            arg_values.push(val);
        }
        // Call the function with receiver as first argument
        return exec_function_with_values(&func, &arg_values, env, functions, classes, enums, impl_methods);
    }

    // E1013 - Unknown Method (with helpful hints for common conversions)
    let mut ctx = ErrorContext::new().with_code(codes::UNKNOWN_METHOD);

    // Handle special case: method on function value (user probably forgot to call the function)
    if recv_val.type_name() == "function" {
        let func_name = match &recv_val {
            Value::Function { name, .. } => name.clone(),
            Value::Lambda { .. } => "<lambda>".to_string(),
            Value::BlockClosure { .. } => "<block>".to_string(),
            Value::NativeFunction(nf) => format!("<native:{}>", nf.name),
            _ => "<unknown>".to_string(),
        };
        ctx = ctx.with_help(format!(
            "you have a function value, not its result. Did you mean to call it? Try: {}().{}()",
            func_name, method
        ));
        return Err(CompileError::semantic_with_context(
            format!(
                "method `{}` not found on type `function` (function '{}' was not called)",
                method, func_name
            ),
            ctx,
        ));
    }

    // Last resort: a present optional is stored as its bare payload (`None` is
    // `Value::Nil`), so an Option method invoked on a present *primitive* optional
    // (e.g. `mj: i32? = 7; mj.unwrap_or(9)`) reaches this general "method not
    // found" point. Mirrors the Object-path fallback and the `Value::Nil => None`
    // arm so typed optionals get the full Option API regardless of payload type.
    if let Some(result) =
        try_bare_some_option_method(&recv_val, method, args, env, functions, classes, enums, impl_methods)?
    {
        return Ok(result);
    }

    let hint = match method {
        "to_f64" | "to_f32" | "to_float" => {
            Some("use implicit conversion (e.g., `float_val / int_val` auto-converts) or explicit cast: `val as f64`")
        }
        "to_i64" | "to_i32" | "to_int" => Some("use explicit cast: `val as i64` or `val as i32`"),
        "to_str" | "to_string" | "toString" => Some("use `str(val)` function or f-string: `f\"{val}\"`"),
        _ => None,
    };

    // Env-gated deep diagnostics for "method not found" on mis-typed receivers
    // (e.g. a struct field decoding as raw i64): the Rust backtrace pins the
    // interp dispatch path when the .spl-level location is unknown.
    if std::env::var("SIMPLE_INTERP_OOB_DEBUG").is_ok() {
        eprintln!(
            "[mnf-debug] method={} recv_type={}\n[mnf-debug-bt] {}",
            method,
            recv_val.type_name(),
            std::backtrace::Backtrace::force_capture()
        );
    }

    // DEBUG: Add receiver value info directly to error message to help diagnose type issues
    let receiver_debug = format!(
        " (receiver value: {})",
        recv_val.to_display_string().chars().take(200).collect::<String>()
    );

    if let Some(hint_text) = hint {
        ctx = ctx.with_help(hint_text);
        Err(CompileError::semantic_with_context(
            format!(
                "method `{}` not found on type `{}`{}",
                method,
                recv_val.type_name(),
                receiver_debug
            ),
            ctx,
        ))
    } else {
        ctx = ctx.with_help("check that the method is defined for this type");
        Err(CompileError::semantic_with_context(
            format!(
                "method `{}` not found on type `{}`{}",
                method,
                recv_val.type_name(),
                receiver_debug
            ),
            ctx,
        ))
    }
}

#[cfg(test)]
mod module_fallback_tests {
    use super::*;
    use simple_parser::ast::Node;
    use simple_parser::Parser;

    #[test]
    fn class_missing_from_env_does_not_call_colliding_bare_function() {
        let module = Parser::new(
            r#"class CollisionSpan:
    static fn empty() -> i32: 17

fn empty(shape: i64) -> i32: shape as i32"#,
        )
        .parse()
        .expect("parse collision fixture");
        let mut functions = HashMap::new();
        let mut classes = HashMap::new();
        for node in module.items {
            match node {
                Node::Class(def) => {
                    classes.insert(def.name.clone(), Arc::new(def));
                }
                Node::Function(def) => {
                    functions.insert(def.name.clone(), Arc::new(def));
                }
                _ => {}
            }
        }
        let mut env = Env::new();
        let receiver = Box::new(Expr::Identifier("CollisionSpan".to_string()));
        let result = evaluate_method_call(
            &receiver,
            "empty",
            &[],
            &mut env,
            &mut functions,
            &mut classes,
            &Enums::new(),
            &ImplMethods::new(),
        )
        .expect("resolve class static method");
        assert_eq!(result, Value::Int(17));
    }
}

/// Evaluate a method call and return both the result and the potentially modified self.
/// This is used when we need to persist mutations to self back to the calling environment.
#[allow(clippy::borrowed_box, clippy::too_many_arguments)] // reason: Box<dyn Trait> dispatch with ABI-locked entry; refactoring deferred
pub(crate) fn evaluate_method_call_with_self_update(
    receiver: &Box<Expr>,
    method: &str,
    args: &[Argument],
    env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<(Value, Option<Value>), CompileError> {
    // Builtin text static methods — intercept before evaluate_expr to avoid
    // "variable `text` not found" when the receiver is the builtin type name.
    if let Expr::Identifier(module_name) = receiver.as_ref() {
        if method == "new" && matches!(module_name.as_str(), "Map" | "Dict" | "HashMap" | "BTreeMap") {
            let value = Value::Dict(Arc::new(HashMap::new()));
            return Ok((value, None));
        }
        if method == "new" && BITFIELDS.with(|cell| cell.borrow().contains_key(module_name)) {
            let value = super::interpreter_call::instantiate_bitfield_from_args(
                module_name,
                args,
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )?;
            return Ok((value, None));
        }
        if module_name == "text" && method == "from_char_code" {
            let evaluated_args: Vec<Value> = args
                .iter()
                .map(|a| evaluate_expr(&a.value, env, functions, classes, enums, impl_methods))
                .collect::<Result<Vec<_>, _>>()?;
            let code = match evaluated_args.first() {
                Some(Value::Int(i)) => *i,
                _ => 0,
            };
            let ch = char::from_u32(code as u32).unwrap_or('\0');
            return Ok((Value::text(ch.to_string()), None));
        }
    }

    let recv_val = evaluate_expr(receiver, env, functions, classes, enums, impl_methods)?.deref_pointer();

    // Only handle Object methods with self mutation
    if let Value::Object { ref class, ref fields } = recv_val {
        // Try to find and execute the method
        if let Some((result, updated_self)) = special::find_and_exec_method_with_self(
            method,
            args,
            class.as_str(),
            fields,
            env,
            functions,
            classes,
            enums,
            impl_methods,
        )? {
            return Ok((result, Some(updated_self)));
        }
        if let Some(field_value) = fields.get(method) {
            match field_value {
                Value::Lambda {
                    params,
                    body,
                    env: captured_env,
                } => {
                    let mut arg_vals = Vec::new();
                    for arg in args {
                        arg_vals.push(evaluate_expr(&arg.value, env, functions, classes, enums, impl_methods)?);
                    }
                    let mut local_env = Env::clone(captured_env);
                    for (i, param) in params.iter().enumerate() {
                        if let Some(val) = arg_vals.get(i) {
                            local_env.insert(param.clone(), val.clone());
                        }
                    }
                    let result = evaluate_expr(body.as_ref(), &mut local_env, functions, classes, enums, impl_methods)?;
                    return Ok((result, None));
                }
                Value::Function { def, captured_env, .. } => {
                    let result = exec_function_with_captured_env(
                        def,
                        args,
                        env,
                        &mut Env::clone(captured_env),
                        functions,
                        classes,
                        enums,
                        impl_methods,
                    )?;
                    return Ok((result, None));
                }
                _ => {}
            }
        }
        // Try method_missing hook
        if let Some(result) = try_method_missing(
            method,
            args,
            class.as_str(),
            fields,
            env,
            functions,
            classes,
            enums,
            impl_methods,
        )? {
            // method_missing returns just a result, self is not mutated
            return Ok((result, None));
        }
        if let Some(result) =
            try_bare_some_option_method(&recv_val, method, args, env, functions, classes, enums, impl_methods)?
        {
            return Ok((result, None));
        }
        // UFCS Fallback: Try to find a free function with the method name
        if let Some(func) = functions.get(method).cloned() {
            // Evaluate all arguments to values
            let mut arg_values = vec![recv_val.clone()]; // Receiver becomes first argument
            for arg in args {
                let val = evaluate_expr(&arg.value, env, functions, classes, enums, impl_methods)?;
                arg_values.push(val);
            }
            // Call the function with receiver as first argument
            let result = exec_function_with_values(&func, &arg_values, env, functions, classes, enums, impl_methods)?;
            return Ok((result, None)); // UFCS calls don't mutate self
        }
        // Collect available methods for typo suggestion
        let mut available_methods: Vec<&str> = Vec::new();
        if let Some(methods) = impl_methods.get(class.as_str()) {
            available_methods.extend(methods.iter().map(|m| m.name.as_str()));
        }
        available_methods.extend(["new", "to_string", "clone", "equals"].iter().copied());
        bail_unknown_method!(method, class.as_str(), available_methods);
    }

    // For non-objects (Array, Dict, String, etc.), check if the method returns a mutated value
    let result =
        evaluate_method_call(receiver, method, args, env, functions, classes, enums, impl_methods).map_err(|e| {
            // Env-gated: names the receiver EXPRESSION (not just its value) so a
            // "method not found on i64" can be traced to the .spl source site.
            if std::env::var("SIMPLE_INTERP_OOB_DEBUG").is_ok() {
                let recv_dbg = format!("{:?}", receiver);
                eprintln!(
                    "[mnf-expr] method={} recv_expr={}",
                    method,
                    &recv_dbg[..recv_dbg.len().min(400)]
                );
            }
            e
        })?;

    // Only propagate self-update for an allow-list of known in-place mutating methods.
    // Previously this used a type-discriminant heuristic ("same type in/out = mutating"),
    // but that wrongly treated non-mutating methods that happen to return the same type
    // (e.g. `String.slice`, `String.trim`, `String.replace`, `Array.slice`,
    // `Array.filter`, `Array.map`) as mutations, clobbering the receiver variable with
    // the returned sub-value. Strings in Simple are value types with NO mutating
    // methods — every "mutating" string op returns a new string. Arrays and dicts have
    // a small fixed set of mutators, listed below.
    const MUTATING_METHODS: &[&str] = &[
        // Array / Vec / List in-place mutators
        "push",
        "push_back",
        "push_front",
        "pop",
        "pop_back",
        "pop_front",
        "append",
        "prepend",
        "insert",
        "remove",
        "remove_at",
        "remove_first",
        "remove_last",
        "clear",
        "extend",
        "sort",
        "sort_by",
        "sort_by_key",
        "reverse",
        "shuffle",
        "dedup",
        "retain",
        "resize",
        "fill",
        "swap",
        "rotate_left",
        "rotate_right",
        "truncate",
        "drain",
        // Bulk in-place span copy (returns the COUNT, receiver derived below like `pop`)
        "write_span",
        // Dict / Map in-place mutators
        "update",
        "set",
        "set_default",
        "merge",
        "delete",
    ];
    // `pop` is the ONE mutator in the list above whose expression result is not the
    // mutated receiver: it yields the popped ELEMENT (see the contract cited in
    // interpreter_method/collections.rs). The same-discriminant test below therefore
    // cannot recover the write-back value for it — `Int` vs `Array` never matches, so
    // it would compute `updated_self = None` and SILENTLY DROP the mutation for every
    // field/index/deep place (`self.gray_stack.pop()` in src/lib/nogc_sync_mut/gc.spl,
    // `self.connections.pop()` in src/lib/nogc_sync_mut/redis/pool.spl). Derive the
    // trimmed receiver from `recv_val` directly instead. Popping an empty array is a
    // no-op, so it needs no write-back.
    if method == "pop" {
        if let Value::Array(arr) = &recv_val {
            if arr.is_empty() {
                return Ok((result, None));
            }
            let mut trimmed = arr.as_ref().clone();
            trimmed.pop();
            return Ok((result, Some(Value::array(trimmed))));
        }
        if let Value::ByteArray(bytes) = &recv_val {
            if bytes.is_empty() {
                return Ok((result, None));
            }
            let mut trimmed = bytes.as_ref().clone();
            trimmed.pop();
            return Ok((result, Some(Value::byte_array(trimmed))));
        }
    }

    // `remove(index)` on an ARRAY is the second such mutator, for exactly the
    // same reason and with exactly the same hazard. As of the 2026-08-08 contract
    // fix its expression result is the REMOVED ELEMENT, not the mutated array, so
    // the same-discriminant test below computes `updated_self = None` (`Int` vs
    // `Array` never matches) and would SILENTLY DROP the removal for every
    // field/index/deep place — e.g. `self.queue.remove(0)` would return the right
    // element while leaving `self.queue` untouched. That is the identical failure
    // mode the `pop` block above exists to prevent, so derive the shortened
    // receiver from `recv_val` directly here too.
    //
    // Dict `remove(key)` is deliberately NOT handled here: its result is the
    // removed VALUE and its receiver is a Dict, so the discriminant test misses
    // it as well — but that is pre-existing behaviour this contract fix does not
    // touch, and changing it belongs to its own lane with its own evidence.
    // doc/08_tracking/bug/array_remove_returns_mutated_array_not_removed_element_2026-07-20.md
    if method == "remove" {
        if let Value::Array(arr) = &recv_val {
            // Re-evaluate the index argument. Cheap (an index expression) and it
            // keeps this block independent of the arm that produced `result`.
            let idx = match args.first() {
                Some(a) => evaluate_expr(&a.value, env, functions, classes, enums, impl_methods)?
                    .as_int()
                    .unwrap_or(-1),
                None => -1,
            };
            // Out of range is a no-op, so there is nothing to write back. This
            // also covers the negative/non-integer cases via the -1 default.
            if idx < 0 || idx as usize >= arr.len() {
                return Ok((result, None));
            }
            let mut shortened = arr.as_ref().clone();
            shortened.remove(idx as usize);
            return Ok((result, Some(Value::array(shortened))));
        }
        if let Value::ByteArray(bytes) = &recv_val {
            let idx = match args.first() {
                Some(a) => evaluate_expr(&a.value, env, functions, classes, enums, impl_methods)?
                    .as_int()
                    .unwrap_or(-1),
                None => -1,
            };
            if idx < 0 || idx as usize >= bytes.len() {
                return Ok((result, None));
            }
            let mut shortened = bytes.as_ref().clone();
            shortened.remove(idx as usize);
            return Ok((result, Some(Value::byte_array(shortened))));
        }
    }

    // `write_span(src, dst_off, src_off, count)` is the third mutator whose
    // expression result is not the mutated receiver: it yields the COUNT WRITTEN
    // (`Int` vs `Array` never matches the discriminant test below), so — exactly
    // like `pop` and `remove` above — the mutated receiver must be re-derived from
    // `recv_val` here or the mutation would be SILENTLY DROPPED for every
    // field/index/deep place. Re-evaluating the arguments is cheap (identifiers /
    // integer expressions) and keeps this block independent of the arm that
    // produced `result`. Bounds were already validated by the arm (shared kernel
    // `collections::array_write_span`), which errored before reaching here.
    if method == "write_span" {
        if let Value::Array(arr) = &recv_val {
            let src = match args.first() {
                Some(a) => evaluate_expr(&a.value, env, functions, classes, enums, impl_methods)?,
                None => Value::Nil,
            };
            let mut ints = [-1i64, -1, 0];
            for (slot, (arg_i, dflt)) in ints.iter_mut().zip([(1usize, -1i64), (2, -1), (3, 0)]) {
                if let Some(a) = args.get(arg_i) {
                    *slot = evaluate_expr(&a.value, env, functions, classes, enums, impl_methods)?
                        .as_int()
                        .unwrap_or(dflt);
                } else {
                    *slot = dflt;
                }
            }
            let (dst_off, src_off, count) = (ints[0], ints[1], ints[2]);
            if count <= 0 {
                return Ok((result, None));
            }
            let mut updated = arr.as_ref().clone();
            collections::array_write_span(&mut updated, &src, dst_off, src_off, count)?;
            return Ok((result, Some(Value::array(updated))));
        }
    }

    // TEXT IS A VALUE TYPE: never rebind a text receiver, for ANY method.
    //
    // The list above is an ARRAY/DICT mutator list. Four of its entries —
    // `push`, `pop`, `clear`, `reverse` — also name real methods on text, and
    // every one of those text arms in `interpreter_method/string.rs` already
    // returns a NEW text and documents that it does ("strings are immutable").
    // The same-discriminant test below could not tell the two apart: `Str` in,
    // `Str` out, so it wrote the new text back over the receiver binding and
    // turned three of them into in-place mutations. Measured before this guard,
    // on `var t = "abc"`:
    //
    // ```text
    // t.push("d")    # -> "abcd" AND t == "abcd"   (rebound)
    // t.clear()      # -> ""     AND t == ""       (rebound)
    // t.reverse()    # -> "cba"  AND t == "cba"    (rebound)
    // ```
    //
    // That contradicts this file's own rule, stated at the head of
    // MUTATING_METHODS: "Strings in Simple are value types with NO mutating
    // methods — every 'mutating' string op returns a new string." It also
    // diverged from every compiled lane, which leaves a text receiver alone.
    // `t.rev()` / `t.reversed()` were already correct, purely because those
    // spellings are absent from the list — the guard makes that an invariant
    // instead of an accident, so a future addition to MUTATING_METHODS cannot
    // silently re-break text.
    //
    // `StrBytes` is text too (a raw-byte text fragment; see `value.rs`), so it
    // is covered by the same rule.
    if matches!(recv_val, Value::Str(_) | Value::StrBytes(_)) {
        return Ok((result, None));
    }

    // A packed byte mutator deliberately widens to the legacy generic array
    // when a pushed/inserted element is not representable as u8. That changes
    // the enum discriminant, so the generic same-discriminant write-back gate
    // below cannot observe it. Widening is nevertheless a receiver mutation.
    if matches!(recv_val, Value::ByteArray(_))
        && MUTATING_METHODS.contains(&method)
        && matches!(result, Value::ByteArray(_) | Value::Array(_))
    {
        return Ok((result.clone(), Some(result)));
    }

    let updated_self =
        if MUTATING_METHODS.contains(&method) && std::mem::discriminant(&result) == std::mem::discriminant(&recv_val) {
            Some(result.clone())
        } else {
            None
        };
    Ok((result, updated_self))
}

#[cfg(test)]
mod tests {
    use super::*;

    // Regression test: me.field as a direct argument to a nested me fn call must
    // not produce "self not found". The bug was that the two typed-dict dispatch
    // paths in evaluate_method_call mutated outer_env with self=recv_val before
    // calling exec_function(..., None), causing arg expressions to evaluate in a
    // scope where self was already rebound to the callee's receiver.
    // Fix: pass self_fields via self_ctx instead of mutating outer_env.
    #[test]
    fn me_field_as_direct_arg_to_me_fn_does_not_error() {
        use simple_parser::Parser;
        use crate::interpreter::evaluate_module;
        let source = r#"
class Counter:
    var count: i64 = 0

    me fn add(n: i64) -> i64:
        return me.count + n

    me fn double_add() -> i64:
        return me.add(me.count)

var c = Counter { count: 5 }
main = c.double_add()
"#;
        let mut parser = Parser::new(source);
        let module = parser.parse().expect("parse");
        let result = evaluate_module(&module.items).expect("me.field as direct arg must not error");
        assert_eq!(result, 10, "double_add() should return count + count = 10");
    }

    /// TEXT IS A VALUE TYPE: no method rebinds a text receiver, and each of the
    /// four array-mutator NAMES that also exist on text evaluates to the pure
    /// result its `interpreter_method/string.rs` arm always documented.
    ///
    /// Expectations are HAND-COMPUTED from this file's own rule (see the
    /// comment above `MUTATING_METHODS`) — never from agreement with another
    /// engine, which would have scored the old behaviour a PASS on `reverse`
    /// (both engines returned `"cba"`; they disagreed only on the receiver).
    ///
    /// Before the text guard in `evaluate_method_call_with_self_update`,
    /// `push`, `clear` and `reverse` each REBOUND `t`, so the `check(t, "abc")`
    /// half of every one of those three rows returned 0.
    #[test]
    fn text_receiver_is_never_rebound_by_an_array_mutator_name() {
        use crate::interpreter::evaluate_module;
        use simple_parser::Parser;

        // (method call on `var t = "abc"`, expected VALUE of the expression)
        let cases: &[(&str, &str)] = &[
            ("t.push(\"d\")", "abcd"),
            ("t.pop()", "c"),
            ("t.clear()", ""),
            ("t.reverse()", "cba"),
            ("t.rev()", "cba"),
            ("t.reversed()", "cba"),
        ];
        for (expr, expected) in cases {
            let source = format!(
                "fn check(a: text, b: text) -> i64:\n    \
                 if a == b:\n        return 1\n    return 0\n\n\
                 var t = \"abc\"\nval r = {expr}\n\
                 main = check(r, \"{expected}\") * 10 + check(t, \"abc\")\n"
            );
            let mut parser = Parser::new(&source);
            let module = parser.parse().unwrap_or_else(|e| panic!("parse {expr}: {e:?}"));
            let result = evaluate_module(&module.items).unwrap_or_else(|e| panic!("evaluate {expr}: {e:?}"));
            assert_eq!(
                result, 11,
                "{expr}: tens digit = expression value is {expected:?}, \
                 units digit = receiver `t` is still \"abc\""
            );
        }
    }

    #[test]
    fn numeric_ordering_compares_unsigned_matcher_values() {
        assert_eq!(
            numeric_ordering(
                &Value::UInt {
                    value: 117_440_512,
                    width: 64,
                },
                &Value::Int(0),
            ),
            Some(Ordering::Greater),
        );
        assert_eq!(
            numeric_ordering(
                &Value::UInt {
                    value: 2_264_924_160,
                    width: 64,
                },
                &Value::UInt {
                    value: 2_147_483_648,
                    width: 64,
                },
            ),
            Some(Ordering::Greater),
        );
        assert_eq!(
            numeric_ordering(
                &Value::Int(-1),
                &Value::UInt {
                    value: u64::MAX,
                    width: 64,
                },
            ),
            Some(Ordering::Less),
        );
    }
}
