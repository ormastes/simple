//! Special type methods: Unit, Option, Result, Mock, Future, Channel, ThreadPool, TraitObject, Object, Constructor

pub mod types;
pub mod mock;
pub mod concurrency;
pub mod objects;
pub mod execution;

// Re-export public API
pub use types::{handle_unit_methods, handle_option_methods, handle_result_methods};
pub use mock::handle_mock_methods;
pub use concurrency::{handle_future_methods, handle_channel_methods, handle_threadpool_methods};
pub use objects::{handle_trait_object_methods, handle_constructor_methods};
pub use execution::{find_and_exec_method_with_self, exec_function_with_self_return};
