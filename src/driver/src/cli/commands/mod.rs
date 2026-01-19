//! Command handler modules for the Simple CLI
//!
//! This module organizes command handlers into focused submodules,
//! each under 300 lines for better maintainability.

pub mod arg_parsing;
pub mod compile_commands;
pub mod env_commands;
pub mod misc_commands;
pub mod pkg_commands;
pub mod startup;
pub mod web_commands;

// Re-export commonly used types and functions
pub use arg_parsing::{filter_internal_flags, parse_lang_flag, GlobalFlags};
pub use compile_commands::{handle_compile, handle_linkers, handle_targets};
pub use env_commands::handle_env;
pub use misc_commands::{handle_diagram, handle_lock, handle_run};
pub use pkg_commands::{
    handle_add, handle_cache, handle_init, handle_install, handle_list, handle_remove,
    handle_tree, handle_update,
};
pub use startup::{
    allocate_resources, early_startup, exit_with_metrics, init_metrics, start_prefetch,
    wait_for_prefetch,
};
pub use web_commands::handle_web;
