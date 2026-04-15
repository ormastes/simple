//! Module definition merging for the Simple interpreter.
//!
//! This module handles merging module definitions into global state
//! and collecting exports.

use std::collections::HashMap;
use std::sync::Arc;

use simple_parser::ast::{ClassDef, EnumDef, Node};

use crate::error::CompileError;
use crate::value::{Env, Value};

type Enums = HashMap<String, Arc<EnumDef>>;

/// Merge module definitions into global state and collect exports
pub fn merge_module_definitions(
    items: &[Node],
    functions: &mut HashMap<String, Arc<simple_parser::ast::FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &mut Enums,
) -> Result<HashMap<String, Value>, CompileError> {
    let mut exports: HashMap<String, Value> = HashMap::new();

    // First pass: collect all definitions into global maps
    for item in items {
        match item {
            Node::Function(f) => {
                // Add to global functions map
                let arc_f = Arc::new(f.clone());
                functions.insert(f.name.clone(), Arc::clone(&arc_f));

                // Add to exports dict
                let func_value = Value::Function {
                    name: f.name.clone(),
                    def: arc_f,
                    captured_env: Arc::new(Env::new()),
                };
                exports.insert(f.name.clone(), func_value);
            }
            Node::Class(c) => {
                // Add to global classes map
                classes.insert(c.name.clone(), Arc::new(c.clone()));

                // Add to exports dict
                exports.insert(
                    c.name.clone(),
                    Value::Constructor {
                        class_name: c.name.clone(),
                    },
                );
            }
            Node::Enum(e) => {
                // Add to global enums map - this is critical for enum variant access
                enums.insert(e.name.clone(), Arc::new(e.clone()));

                // Export the enum as EnumType for variant construction (EnumName.Variant)
                exports.insert(
                    e.name.clone(),
                    Value::EnumType {
                        enum_name: e.name.clone(),
                    },
                );
            }
            _ => {}
        }
    }

    Ok(exports)
}
