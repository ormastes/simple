//! Interpreter tests - macros

use simple_driver::interpreter::run_code;

#[path = "interpreter_macros/builtin.rs"]
mod builtin;
#[path = "interpreter_macros/field_intro.rs"]
mod field_intro;
#[path = "interpreter_macros/full_syntax.rs"]
mod full_syntax;
#[path = "interpreter_macros/inject.rs"]
mod inject;
#[path = "interpreter_macros/intro.rs"]
mod intro;
#[path = "interpreter_macros/ll1.rs"]
mod ll1;
#[path = "interpreter_macros/parser_validation.rs"]
mod parser_validation;
#[path = "interpreter_macros/recursion.rs"]
mod recursion;
#[path = "interpreter_macros/user_defined.rs"]
mod user_defined;
#[path = "interpreter_macros/variadic.rs"]
mod variadic;
