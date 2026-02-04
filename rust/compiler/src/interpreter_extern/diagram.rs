//! Diagram FFI functions for the Simple language interpreter
//!
//! This module provides interpreter bindings for diagram tracing and generation.

use crate::error::CompileError;
use crate::value::Value;
use simple_runtime::value::diagram_ffi;

/// Enable diagram recording
pub fn rt_diagram_enable(_args: &[Value]) -> Result<Value, CompileError> {
    diagram_ffi::enable_diagrams();
    Ok(Value::Nil)
}

/// Disable diagram recording
pub fn rt_diagram_disable(_args: &[Value]) -> Result<Value, CompileError> {
    diagram_ffi::disable_diagrams();
    Ok(Value::Nil)
}

/// Clear all recorded events
pub fn rt_diagram_clear(_args: &[Value]) -> Result<Value, CompileError> {
    diagram_ffi::clear_diagram_data();
    Ok(Value::Nil)
}

/// Check if diagram recording is enabled
pub fn rt_diagram_is_enabled(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Bool(diagram_ffi::is_diagram_enabled()))
}

/// Trace a method call
pub fn rt_diagram_trace_method(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 2 {
        return Err(CompileError::semantic(
            "rt_diagram_trace_method requires 2 arguments: class_name, method_name",
        ));
    }

    let class_name = match &args[0] {
        Value::Str(s) => s.clone(),
        _ => return Err(CompileError::semantic("class_name must be a string")),
    };

    let method_name = match &args[1] {
        Value::Str(s) => s.clone(),
        _ => return Err(CompileError::semantic("method_name must be a string")),
    };

    diagram_ffi::trace_method(&class_name, &method_name);
    Ok(Value::Nil)
}

/// Trace a method call with arguments
pub fn rt_diagram_trace_method_with_args(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 3 {
        return Err(CompileError::semantic(
            "rt_diagram_trace_method_with_args requires 3 arguments: class_name, method_name, args",
        ));
    }

    let class_name = match &args[0] {
        Value::Str(s) => s.clone(),
        _ => return Err(CompileError::semantic("class_name must be a string")),
    };

    let method_name = match &args[1] {
        Value::Str(s) => s.clone(),
        _ => return Err(CompileError::semantic("method_name must be a string")),
    };

    // Parse args as comma-separated string or array
    let arguments: Vec<String> = match &args[2] {
        Value::Str(s) => s.split(',').map(|a| a.trim().to_string()).collect(),
        Value::Array(items) => items
            .iter()
            .filter_map(|v| match v {
                Value::Str(s) => Some(s.clone()),
                _ => None,
            })
            .collect(),
        _ => vec![],
    };

    diagram_ffi::trace_method_with_args(&class_name, &method_name, &arguments);
    Ok(Value::Nil)
}

/// Trace a return value
pub fn rt_diagram_trace_return(args: &[Value]) -> Result<Value, CompileError> {
    let value = if args.is_empty() {
        None
    } else {
        match &args[0] {
            Value::Str(s) => Some(s.as_str()),
            Value::Nil => None,
            _ => None,
        }
    };

    diagram_ffi::trace_return(value);
    Ok(Value::Nil)
}

/// Mark an entity as architectural
pub fn rt_diagram_mark_architectural(args: &[Value]) -> Result<Value, CompileError> {
    if args.is_empty() {
        return Err(CompileError::semantic(
            "rt_diagram_mark_architectural requires 1 argument: entity",
        ));
    }

    let entity = match &args[0] {
        Value::Str(s) => s.clone(),
        _ => return Err(CompileError::semantic("entity must be a string")),
    };

    diagram_ffi::mark_architectural(&entity);
    Ok(Value::Nil)
}

/// Generate sequence diagram as mermaid string
pub fn rt_diagram_generate_sequence(_args: &[Value]) -> Result<Value, CompileError> {
    let events = diagram_ffi::get_recorded_events();
    let mermaid = generate_sequence_mermaid(&events);
    Ok(Value::Str(mermaid))
}

/// Generate class diagram as mermaid string
pub fn rt_diagram_generate_class(_args: &[Value]) -> Result<Value, CompileError> {
    let events = diagram_ffi::get_recorded_events();
    let mermaid = generate_class_mermaid(&events);
    Ok(Value::Str(mermaid))
}

/// Generate architecture diagram as mermaid string
pub fn rt_diagram_generate_arch(_args: &[Value]) -> Result<Value, CompileError> {
    let events = diagram_ffi::get_recorded_events();
    let arch_entities = diagram_ffi::get_architectural_entities();
    let mermaid = generate_arch_mermaid(&events, &arch_entities);
    Ok(Value::Str(mermaid))
}

/// Free a string (no-op in interpreter, for FFI compatibility)
pub fn rt_diagram_free_string(_args: &[Value]) -> Result<Value, CompileError> {
    // No-op in interpreter - memory is managed by Rust
    Ok(Value::Nil)
}

// ============================================================================
// Helper functions for diagram generation
// ============================================================================

fn generate_sequence_mermaid(events: &[diagram_ffi::CallEvent]) -> String {
    let mut output = String::from("sequenceDiagram\n");

    // Extract participants
    let mut participants: Vec<String> = vec![];
    for event in events {
        if let Some(cls) = &event.callee_class {
            if !participants.contains(cls) {
                participants.push(cls.clone());
            }
        }
    }

    // Add participants
    for p in &participants {
        output.push_str(&format!("    participant {}\n", p));
    }
    output.push('\n');

    // Generate calls
    let mut stack: Vec<String> = vec!["Test".to_string()];
    for event in events {
        if let Some(cls) = &event.callee_class {
            let caller = stack.last().cloned().unwrap_or_else(|| "Test".to_string());

            match event.call_type {
                diagram_ffi::CallType::Method | diagram_ffi::CallType::Function => {
                    let args = if event.arguments.is_empty() {
                        String::new()
                    } else {
                        event.arguments.join(", ")
                    };
                    output.push_str(&format!(
                        "    {}->>{}:{}{}\n",
                        caller,
                        cls,
                        event.callee,
                        if args.is_empty() {
                            String::new()
                        } else {
                            format!("({})", args)
                        }
                    ));
                    stack.push(cls.clone());
                }
                diagram_ffi::CallType::Return => {
                    if stack.len() > 1 {
                        stack.pop();
                        let returnee = stack.last().cloned().unwrap_or_else(|| "Test".to_string());
                        let ret_val = event.return_value.as_deref().unwrap_or("void");
                        output.push_str(&format!("    {}-->>{}:{}\n", cls, returnee, ret_val));
                    }
                }
                diagram_ffi::CallType::Constructor => {
                    output.push_str(&format!("    {}->>{}:new()\n", caller, cls));
                    stack.push(cls.clone());
                }
            }
        }
    }

    output
}

fn generate_class_mermaid(events: &[diagram_ffi::CallEvent]) -> String {
    let mut output = String::from("classDiagram\n");

    // Extract classes and methods
    let mut classes: std::collections::HashMap<String, Vec<String>> = std::collections::HashMap::new();

    for event in events {
        if let Some(cls) = &event.callee_class {
            let methods = classes.entry(cls.clone()).or_default();
            if !methods.contains(&event.callee) {
                methods.push(event.callee.clone());
            }
        }
    }

    // Generate class definitions
    for (cls, methods) in &classes {
        output.push_str(&format!("    class {} {{\n", cls));
        for method in methods {
            output.push_str(&format!("        +{}()\n", method));
        }
        output.push_str("    }\n");
    }

    // Generate relationships
    let mut relationships: Vec<(String, String)> = vec![];
    let mut last_class: Option<String> = None;

    for event in events {
        if let Some(cls) = &event.callee_class {
            if let Some(prev) = &last_class {
                if prev != cls {
                    let rel = (prev.clone(), cls.clone());
                    if !relationships.contains(&rel) {
                        relationships.push(rel);
                    }
                }
            }
            last_class = Some(cls.clone());
        }
    }

    output.push('\n');
    for (from, to) in &relationships {
        output.push_str(&format!("    {} --> {}\n", from, to));
    }

    output
}

fn generate_arch_mermaid(events: &[diagram_ffi::CallEvent], arch_entities: &[String]) -> String {
    let mut output = String::from("flowchart TD\n");

    // Add architectural nodes
    for entity in arch_entities {
        if entity.contains('.') {
            let parts: Vec<&str> = entity.split('.').collect();
            let short_name = parts.last().copied().unwrap_or(entity.as_str());
            output.push_str(&format!("    {}[{}]\n", entity.replace('.', "_"), short_name));
        } else {
            output.push_str(&format!("    {}\n", entity));
        }
    }

    // Extract edges from events between architectural entities
    let mut edges: Vec<(String, String)> = vec![];
    let mut last_arch: Option<String> = None;

    for event in events {
        if let Some(cls) = &event.callee_class {
            if arch_entities.contains(cls) {
                if let Some(prev) = &last_arch {
                    if prev != cls {
                        let edge = (prev.clone(), cls.clone());
                        if !edges.contains(&edge) {
                            edges.push(edge);
                        }
                    }
                }
                last_arch = Some(cls.clone());
            }
        }
    }

    output.push('\n');
    for (from, to) in &edges {
        let from_id = from.replace('.', "_");
        let to_id = to.replace('.', "_");
        output.push_str(&format!("    {} --> {}\n", from_id, to_id));
    }

    output
}
