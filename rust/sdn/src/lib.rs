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
//! # Security
//!
//! SDN provides multiple parsing modes for different trust levels:
//!
//! ## Trusted Input (Default)
//!
//! ```
//! use simple_sdn::parse;
//!
//! let value = parse("name: Alice\nage: 30")?;
//! # Ok::<(), simple_sdn::SdnError>(())
//! ```
//!
//! ## Untrusted Input (Validation)
//!
//! ```
//! use simple_sdn::parse_untrusted;
//!
//! // Rejects: deep nesting, large strings, excessive cells
//! let untrusted_source = "name: Alice\nage: 30";
//! let value = parse_untrusted(untrusted_source)?;
//! # Ok::<(), simple_sdn::SdnError>(())
//! ```
//!
//! ## Configuration Files (Flat Structure)
//!
//! ```
//! use simple_sdn::parse_config;
//!
//! // Rejects: tables, arrays, nesting
//! let config = parse_config("debug: true\nport: 8080")?;
//! # Ok::<(), simple_sdn::SdnError>(())
//! ```
//!
//! ## Safe Keys (Injection Prevention)
//!
//! ```
//! use simple_sdn::parse_safe;
//!
//! // Rejects: __proto__, ../, control chars
//! let source = "user_name: Alice";
//! let value = parse_safe(source)?;
//! # Ok::<(), simple_sdn::SdnError>(())
//! ```
//!
//! ## Custom Policies
//!
//! ```
//! use simple_sdn::{parser::Parser, RestrictedHandler};
//!
//! let source = "name: Alice\nage: 30";
//! let handler = RestrictedHandler::new().without_tables();
//! let mut parser = Parser::new(source);
//! let value = parser.parse_with_handler(handler)?;
//! # Ok::<(), simple_sdn::SdnError>(())
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
//! ratio: 3.15           # float
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
pub mod handler;
pub mod handlers;

// Re-exports for convenience
pub use document::SdnDocument;
pub use error::{Result, SdnError, Span};
pub use parser::{parse, parse_file, parse_untrusted, parse_config, parse_safe};
pub use value::SdnValue;
pub use handler::{DataHandler, OpHandler, SdnHandler};
pub use handlers::{ValueBuilder, NoopHandler, RestrictedHandler, SafeKeyHandler};

/// Parse SDN source into an editable document.
pub fn parse_document(source: &str) -> Result<SdnDocument> {
    SdnDocument::parse(source)
}
