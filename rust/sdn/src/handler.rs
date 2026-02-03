//! Handler traits for SDN parsing
//!
//! This module defines the trait-based architecture for SDN parsing that separates
//! data processing from operation processing. This enables:
//! - Zero-allocation validation (noop handler)
//! - Security policies (restricted handler)
//! - Custom processing pipelines
//!
//! # Architecture
//!
//! - `DataHandler`: Processes primitive values (int, string, bool, etc.)
//! - `OpHandler`: Processes structural operations (dict/array/table begin/end)
//! - `SdnHandler`: Combined trait with `finish()` method
//!
//! # Example
//!
//! ```rust
//! use simple_sdn::{parser::Parser, ValueBuilder};
//!
//! let src = "name: Alice\nage: 30";
//! let mut parser = Parser::new(src);
//! let handler = ValueBuilder::new();
//! let value = parser.parse_with_handler(handler)?;
//! # Ok::<(), simple_sdn::SdnError>(())
//! ```

use crate::error::{Result, Span};

/// Handles primitive data values during parsing
///
/// Each method is called when the parser encounters a primitive value.
/// Implementations can build data structures, validate, or ignore values.
pub trait DataHandler {
    /// Called when a null value is parsed
    fn on_null(&mut self, span: Span) -> Result<()>;

    /// Called when a boolean is parsed
    fn on_bool(&mut self, value: bool, span: Span) -> Result<()>;

    /// Called when an integer is parsed
    fn on_int(&mut self, value: i64, span: Span) -> Result<()>;

    /// Called when a float is parsed
    fn on_float(&mut self, value: f64, span: Span) -> Result<()>;

    /// Called when a string is parsed
    fn on_string(&mut self, value: &str, span: Span) -> Result<()>;
}

/// Handles structural operations during parsing
///
/// Each method is called when the parser enters/exits a container structure.
/// This allows implementations to enforce policies (e.g., "no tables allowed")
/// or track nesting depth without allocating.
pub trait OpHandler {
    /// Begin parsing a dictionary
    fn begin_dict(&mut self, span: Span) -> Result<()>;

    /// Dictionary key encountered (before its value)
    fn dict_key(&mut self, key: &str, span: Span) -> Result<()>;

    /// End of dictionary
    fn end_dict(&mut self) -> Result<()>;

    /// Begin parsing an array
    fn begin_array(&mut self, span: Span) -> Result<()>;

    /// End of array
    fn end_array(&mut self) -> Result<()>;

    /// Begin parsing a table
    fn begin_table(&mut self, fields: Option<&[String]>, types: Option<&[String]>, span: Span) -> Result<()>;

    /// Begin a table row
    fn begin_row(&mut self) -> Result<()>;

    /// End a table row
    fn end_row(&mut self) -> Result<()>;

    /// End of table
    fn end_table(&mut self) -> Result<()>;
}

/// Combined handler trait for SDN parsing
///
/// This trait combines `DataHandler` and `OpHandler` and adds a `finish()`
/// method to produce the final output after parsing completes.
pub trait SdnHandler: DataHandler + OpHandler {
    /// The output type produced by this handler
    type Output;

    /// Called after successful parse to produce final output
    fn finish(self) -> Result<Self::Output>;
}
