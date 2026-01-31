//! Helper to convert SdnValue to handler events
//!
//! This allows us to replay an SdnValue tree through a handler,
//! useful for validation or transformation.

use crate::error::{Result, Span};
use crate::handler::{DataHandler, OpHandler};
use crate::value::SdnValue;

/// Replay an SdnValue through a handler
pub fn replay_value<H: DataHandler + OpHandler>(value: &SdnValue, handler: &mut H) -> Result<()> {
    replay_value_impl(value, handler, Span::default())
}

fn replay_value_impl<H: DataHandler + OpHandler>(
    value: &SdnValue,
    handler: &mut H,
    span: Span,
) -> Result<()> {
    match value {
        SdnValue::Null => handler.on_null(span),
        SdnValue::Bool(b) => handler.on_bool(*b, span),
        SdnValue::Int(i) => handler.on_int(*i, span),
        SdnValue::Float(f) => handler.on_float(*f, span),
        SdnValue::String(s) => handler.on_string(s, span),
        SdnValue::Array(arr) => {
            handler.begin_array(span)?;
            for item in arr {
                replay_value_impl(item, handler, span)?;
            }
            handler.end_array()
        }
        SdnValue::Dict(dict) => {
            handler.begin_dict(span)?;
            for (key, val) in dict {
                handler.dict_key(key, span)?;
                replay_value_impl(val, handler, span)?;
            }
            handler.end_dict()
        }
        SdnValue::Table { fields, types, rows } => {
            handler.begin_table(fields.as_deref(), types.as_deref(), span)?;
            for row in rows {
                handler.begin_row()?;
                for cell in row {
                    replay_value_impl(cell, handler, span)?;
                }
                handler.end_row()?;
            }
            handler.end_table()
        }
    }
}
