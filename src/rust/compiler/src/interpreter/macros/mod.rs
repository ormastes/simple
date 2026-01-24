pub use crate::r#macro::{clear_macro_state, set_macro_trace};
pub(crate) use crate::r#macro::{
    enter_block_scope, enter_class_scope, evaluate_macro_invocation, exit_block_scope, exit_class_scope,
    preprocess_macro_contract_at_definition, queue_tail_injection, take_macro_introduced_symbols,
};
