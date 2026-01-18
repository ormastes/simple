pub use crate::r#macro::set_macro_trace;
pub(crate) use crate::r#macro::{
    enter_block_scope, evaluate_macro_invocation, exit_block_scope, preprocess_macro_contract_at_definition,
    queue_tail_injection, take_macro_introduced_symbols,
};
