// Async/Promise support for function execution

use crate::value::*;
use simple_parser::ast::{Effect, FunctionDef};
use std::collections::HashMap;
use std::sync::Arc;

/// Wrap a value in a Promise (Resolved state) for async function returns.
/// Creates a Promise object with state = PromiseState.Resolved(value).
pub(crate) fn wrap_in_promise(value: Value) -> Value {
    // Don't double-wrap if the value is already a Promise
    if let Value::Object { ref class, .. } = value {
        if class == "Promise" {
            return value;
        }
    }

    let mut fields = HashMap::new();
    fields.insert(
        "state".to_string(),
        Value::Enum {
            enum_name: "PromiseState".to_string(),
            variant: "Resolved".to_string(),
            payload: Some(Box::new(value)),
        },
    );
    fields.insert("callbacks".to_string(), Value::array(vec![]));

    Value::Object {
        class: "Promise".to_string(),
        fields: Arc::new(fields),
    }
}

/// Check if a function is async (has Effect::Async in its effects)
pub(crate) fn is_async_function(func: &FunctionDef) -> bool {
    func.effects.iter().any(|e| matches!(e, Effect::Async))
}

/// Wrap an interpreted async function's result.
///
/// When the running program has registered the std.async `Future` class
/// (the pure-Simple async surface), construct the `Future.from_value`
/// shape — `state: []`, `poll_result: Poll.Ready(value)` — so the call
/// returns a real ready future that `poll()`/`is_ready()` work on. Programs
/// without that class keep the legacy Promise shape.
pub(crate) fn wrap_async_result(value: Value, has_future_class: bool) -> Value {
    if has_future_class {
        let mut fields = HashMap::new();
        fields.insert("state".to_string(), Value::array(vec![]));
        fields.insert(
            "poll_result".to_string(),
            Value::Enum {
                enum_name: "Poll".to_string(),
                variant: "Ready".to_string(),
                payload: Some(Box::new(value)),
            },
        );
        return Value::Object {
            class: "Future".to_string(),
            fields: Arc::new(fields),
        };
    }
    wrap_in_promise(value)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_wrap_in_promise() {
        let value = Value::Int(42);
        let promise = wrap_in_promise(value.clone());

        match promise {
            Value::Object { class, fields } => {
                assert_eq!(class, "Promise");
                assert!(fields.contains_key("state"));
                assert!(fields.contains_key("callbacks"));
            }
            _ => panic!("Expected Promise object"),
        }
    }

    #[test]
    fn test_wrap_in_promise_idempotent() {
        let value = Value::Int(42);
        let promise = wrap_in_promise(value.clone());
        let double_wrapped = wrap_in_promise(promise.clone());

        // Should not double-wrap
        if let Value::Object { ref class, .. } = double_wrapped {
            assert_eq!(class, "Promise");
        } else {
            panic!("Expected Promise object");
        }
    }
}
