// Core function execution for interpreter
// Modular structure - each module < 300 lines

// Helper macros
pub(crate) mod macros;

// Async/Promise support
pub(crate) mod async_support;

// Argument binding and validation
pub(crate) mod arg_binding;

// Lambda execution
pub(crate) mod lambda;

// Core function execution logic
pub(crate) mod function_exec;

// Class instantiation and initialization
pub(crate) mod class_instantiation;

// Dependency injection resolution
pub(crate) mod di_injection;

// AOP around advice support
pub(crate) mod aop_advice;

// Re-export public interface for backward compatibility
pub(crate) use arg_binding::{bind_args, bind_args_with_injected};
pub(crate) use class_instantiation::instantiate_class;
pub(crate) use function_exec::{
    exec_function, exec_function_with_captured_env, exec_function_with_values,
    exec_function_with_values_and_self,
};
pub(crate) use lambda::exec_lambda;

// Re-export types that are part of the public interface
pub(crate) use aop_advice::ProceedContext;
pub(crate) use class_instantiation::IN_NEW_METHOD;
