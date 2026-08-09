//! Default handler that builds SdnValue tree
//!
//! This is the default handler used by `parse()`. It constructs an `SdnValue`
//! tree during parsing, identical to the original parser behavior.

use crate::error::{Result, SdnError, Span};
use crate::handler::{DataHandler, OpHandler, SdnHandler};
use crate::value::SdnValue;
use indexmap::IndexMap;

/// Handler that builds an SdnValue tree during parsing
pub struct ValueBuilder {
    stack: Vec<BuilderFrame>,
    root: Option<SdnValue>,
}

enum BuilderFrame {
    Dict {
        map: IndexMap<String, SdnValue>,
        current_key: Option<String>,
    },
    Array {
        items: Vec<SdnValue>,
    },
    Table {
        fields: Option<Vec<String>>,
        types: Option<Vec<String>>,
        rows: Vec<Vec<SdnValue>>,
        current_row: Option<Vec<SdnValue>>,
    },
}

impl ValueBuilder {
    /// Create a new ValueBuilder
    pub fn new() -> Self {
        Self {
            stack: Vec::new(),
            root: None,
        }
    }

    fn push_value(&mut self, value: SdnValue) {
        match self.stack.last_mut() {
            Some(BuilderFrame::Dict { map, current_key }) => {
                if let Some(key) = current_key.take() {
                    map.insert(key, value);
                }
            }
            Some(BuilderFrame::Array { items }) => {
                items.push(value);
            }
            Some(BuilderFrame::Table {
                current_row: Some(row), ..
            }) => {
                row.push(value);
            }
            None => {
                self.root = Some(value);
            }
            _ => {}
        }
    }
}

impl DataHandler for ValueBuilder {
    fn on_null(&mut self, _span: Span) -> Result<()> {
        self.push_value(SdnValue::Null);
        Ok(())
    }

    fn on_bool(&mut self, value: bool, _span: Span) -> Result<()> {
        self.push_value(SdnValue::Bool(value));
        Ok(())
    }

    fn on_int(&mut self, value: i64, _span: Span) -> Result<()> {
        self.push_value(SdnValue::Int(value));
        Ok(())
    }

    fn on_float(&mut self, value: f64, _span: Span) -> Result<()> {
        self.push_value(SdnValue::Float(value));
        Ok(())
    }

    fn on_string(&mut self, value: &str, _span: Span) -> Result<()> {
        self.push_value(SdnValue::String(value.to_string()));
        Ok(())
    }
}

impl OpHandler for ValueBuilder {
    fn begin_dict(&mut self, _span: Span) -> Result<()> {
        self.stack.push(BuilderFrame::Dict {
            map: IndexMap::new(),
            current_key: None,
        });
        Ok(())
    }

    fn dict_key(&mut self, key: &str, _span: Span) -> Result<()> {
        if let Some(BuilderFrame::Dict { current_key, .. }) = self.stack.last_mut() {
            *current_key = Some(key.to_string());
        }
        Ok(())
    }

    fn end_dict(&mut self) -> Result<()> {
        if let Some(BuilderFrame::Dict { map, .. }) = self.stack.pop() {
            self.push_value(SdnValue::Dict(map));
        }
        Ok(())
    }

    fn begin_array(&mut self, _span: Span) -> Result<()> {
        self.stack.push(BuilderFrame::Array { items: Vec::new() });
        Ok(())
    }

    fn end_array(&mut self) -> Result<()> {
        if let Some(BuilderFrame::Array { items }) = self.stack.pop() {
            self.push_value(SdnValue::Array(items));
        }
        Ok(())
    }

    fn begin_table(&mut self, fields: Option<&[String]>, types: Option<&[String]>, _span: Span) -> Result<()> {
        self.stack.push(BuilderFrame::Table {
            fields: fields.map(|f| f.to_vec()),
            types: types.map(|t| t.to_vec()),
            rows: Vec::new(),
            current_row: None,
        });
        Ok(())
    }

    fn begin_row(&mut self) -> Result<()> {
        if let Some(BuilderFrame::Table { current_row, .. }) = self.stack.last_mut() {
            *current_row = Some(Vec::new());
        }
        Ok(())
    }

    fn end_row(&mut self) -> Result<()> {
        if let Some(BuilderFrame::Table { rows, current_row, .. }) = self.stack.last_mut() {
            if let Some(row) = current_row.take() {
                rows.push(row);
            }
        }
        Ok(())
    }

    fn end_table(&mut self) -> Result<()> {
        if let Some(BuilderFrame::Table {
            fields, types, rows, ..
        }) = self.stack.pop()
        {
            self.push_value(SdnValue::Table { fields, types, rows });
        }
        Ok(())
    }
}

impl SdnHandler for ValueBuilder {
    type Output = SdnValue;

    fn finish(self) -> Result<SdnValue> {
        self.root.ok_or_else(|| SdnError::ParseError {
            message: "No value parsed".to_string(),
            span: None,
        })
    }
}

impl Default for ValueBuilder {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_value_builder_basic() {
        let mut builder = ValueBuilder::new();
        builder.begin_dict(Span::default()).unwrap();
        builder.dict_key("name", Span::default()).unwrap();
        builder.on_string("Alice", Span::default()).unwrap();
        builder.dict_key("age", Span::default()).unwrap();
        builder.on_int(30, Span::default()).unwrap();
        builder.end_dict().unwrap();
        let value = builder.finish().unwrap();
        assert_eq!(value.get("name").and_then(|v| v.as_str()), Some("Alice"));
        assert_eq!(value.get("age").and_then(|v| v.as_i64()), Some(30));
    }

    #[test]
    fn test_value_builder_nested() {
        let mut builder = ValueBuilder::new();
        builder.begin_dict(Span::default()).unwrap();
        builder.dict_key("server", Span::default()).unwrap();
        builder.begin_dict(Span::default()).unwrap();
        builder.dict_key("host", Span::default()).unwrap();
        builder.on_string("localhost", Span::default()).unwrap();
        builder.end_dict().unwrap();
        builder.end_dict().unwrap();
        let value = builder.finish().unwrap();
        assert_eq!(
            value.get_path("server.host").and_then(|v| v.as_str()),
            Some("localhost")
        );
    }

    #[test]
    fn test_value_builder_array() {
        let mut builder = ValueBuilder::new();
        builder.begin_dict(Span::default()).unwrap();
        builder.dict_key("items", Span::default()).unwrap();
        builder.begin_array(Span::default()).unwrap();
        builder.on_int(1, Span::default()).unwrap();
        builder.on_int(2, Span::default()).unwrap();
        builder.on_int(3, Span::default()).unwrap();
        builder.end_array().unwrap();
        builder.end_dict().unwrap();
        let value = builder.finish().unwrap();
        let arr = value.get("items").and_then(|v| v.as_array()).unwrap();
        assert_eq!(arr.len(), 3);
        assert_eq!(arr[0].as_i64(), Some(1));
    }
}
