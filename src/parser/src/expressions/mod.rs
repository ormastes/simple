//! Expression parsing module
//!
//! This module contains all expression parsing logic for the Simple language parser.
//! It implements a Pratt parser (precedence climbing) for binary operators.

mod core;
mod no_paren;
mod binary;
mod postfix;
mod helpers;
mod primary;
