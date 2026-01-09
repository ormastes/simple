//! Special type methods: Unit, Option, Result, Mock, Future, Channel, ThreadPool, TraitObject, Object, Constructor

pub mod concurrency;
pub mod execution;
pub mod mock;
pub mod objects;
pub mod types;

// Re-export public API
pub use concurrency::{handle_channel_methods, handle_future_methods, handle_threadpool_methods};
pub use execution::{exec_function_with_self_return, find_and_exec_method_with_self};
pub use mock::handle_mock_methods;
pub use objects::{handle_constructor_methods, handle_trait_object_methods};
pub use types::{handle_option_methods, handle_result_methods, handle_unit_methods};
