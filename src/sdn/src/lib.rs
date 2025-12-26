//! SDN - Simple Data Notation
//!
//! A minimal, token-efficient data notation format for configuration files and embedded data.
//!
//! # Features
//!
//! - Minimal syntax with no unnecessary punctuation
//! - One-pass LL(2) parsing
//! - Token efficient for LLM context windows
//! - Human readable with clear visual structure
//! - Embeddable as standalone files or in Simple code
//!
//! # Quick Start
//!
//! ```
//! use simple_sdn::{parse, SdnValue};
//!
//! let src = r#"
//! name: Alice
//! age: 30
//! server:
//!     host: localhost
//!     port: 8080
//! "#;
//!
//! let doc = parse(src).unwrap();
//! assert_eq!(doc.get("name").and_then(|v| v.as_str()), Some("Alice"));
//! assert_eq!(doc.get_path("server.port").and_then(|v| v.as_i64()), Some(8080));
//! ```
//!
//! # Document API
//!
//! For editable documents with formatting preservation:
//!
//! ```
//! use simple_sdn::SdnDocument;
//!
//! let mut doc = SdnDocument::parse("port: 8080").unwrap();
//! doc.set("port", simple_sdn::SdnValue::Int(9090)).unwrap();
//! let output = doc.to_sdn();
//! ```
//!
//! # SDN Syntax
//!
//! ## Values
//!
//! ```sdn
//! name: Alice           # bare string
//! message: "Hello"      # quoted string
//! age: 30               # integer
//! ratio: 3.14           # float
//! active: true          # boolean
//! empty: null           # null
//! ```
//!
//! ## Dict (short and long form)
//!
//! ```sdn
//! point = {x: 10, y: 20}    # short form (=)
//!
//! server:                    # long form (:)
//!     host: localhost
//!     port: 8080
//! ```
//!
//! ## Array (short and long form)
//!
//! ```sdn
//! names = [Alice, Bob]      # short form (=)
//!
//! features:                  # long form (:)
//!     auth
//!     logging
//! ```
//!
//! ## Tables
//!
//! ```sdn
//! # Named table
//! users |id, name|
//!     1, Alice
//!     2, Bob
//!
//! # Typed table
//! coords: table{i32, i32} = [(10, 20), (30, 40)]
//! ```

pub mod document;
pub mod error;
pub mod lexer;
pub mod parser;
pub mod value;

// Re-exports for convenience
pub use document::SdnDocument;
pub use error::{Result, SdnError, Span};
pub use parser::{parse, parse_file};
pub use value::SdnValue;

/// Parse SDN source into an editable document.
pub fn parse_document(source: &str) -> Result<SdnDocument> {
    SdnDocument::parse(source)
}
