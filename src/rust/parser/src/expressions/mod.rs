//! Expression parsing module
//!
//! This module contains all expression parsing logic for the Simple language parser.
//! It implements a Pratt parser (precedence climbing) for binary operators.

mod binary;
mod core;
mod helpers;
mod no_paren;
mod postfix;
mod primary;
