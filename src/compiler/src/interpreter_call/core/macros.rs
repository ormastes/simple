// Helper Macros for Reducing Duplication

use crate::interpreter_unit::{is_unit_type, validate_unit_type};
use crate::value::*;
use simple_parser::ast::Type;

/// Wrap value in TraitObject if parameter has DynTrait type
macro_rules! wrap_trait_object {
    ($val:expr, $param_ty:expr) => {
        if let Some(Type::DynTrait(trait_name)) = $param_ty {
            Value::TraitObject {
                trait_name: trait_name.clone(),
                inner: Box::new($val),
            }
        } else {
            $val
        }
    };
}

/// Validate unit type for parameter or return type
macro_rules! validate_unit {
    ($val:expr, $ty:expr, $context:expr) => {
        if let Some(Type::Simple(type_name)) = $ty {
            if is_unit_type(type_name) {
                if let Err(e) = validate_unit_type($val, type_name) {
                    bail_semantic!("{}: {}", $context, e);
                }
            }
        }
    };
}

/// Check effect compatibility and execute with effect context
macro_rules! with_effect_check {
    ($func:expr, $body:expr) => {{
        crate::effects::check_call_compatibility(&$func.name, &$func.effects)?;
        crate::interpreter::with_effect_context(&$func.effects, || $body)
    }};
}

/// Extract result from exec_block_fn return value
macro_rules! extract_block_result {
    ($block_exec:expr) => {
        match $block_exec {
            Ok((crate::interpreter::Control::Return(v), _)) => v,
            Ok((_, Some(v))) => v,
            Ok((_, None)) => Value::Nil,
            Err(crate::error::CompileError::TryError(val)) => val,
            Err(e) => return Err(e),
        }
    };
}

pub(crate) use extract_block_result;
pub(crate) use validate_unit;
pub(crate) use with_effect_check;
pub(crate) use wrap_trait_object;
