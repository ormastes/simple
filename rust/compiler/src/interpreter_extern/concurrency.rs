// Concurrency Operations (Threads and Channels)
//
// Thread operations for isolated thread spawning and management
// Channel operations for thread communication

use crate::concurrent_providers::ConcurrentBackend;
use crate::concurrent_providers::registry::ConcurrentProviderRegistry;
use crate::error::CompileError;
use crate::interpreter::interpreter_state::{get_concurrent_registry, set_concurrent_registry};
use crate::value::{Env, Value};
use simple_parser::ast::{ClassDef, EnumDef, Expr, FunctionDef};
use std::sync::mpsc::{channel, Sender, Receiver};
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::Duration;
use std::collections::HashMap;

// Import interpreter functions from parent module
// super::super refers to the interpreter module (super is interpreter_extern)
use super::super::{evaluate_expr, exec_block_value};

type Enums = HashMap<String, EnumDef>;
type ImplMethods = HashMap<String, Vec<FunctionDef>>;

// Global storage for thread handles, channels, and results
lazy_static::lazy_static! {
    static ref THREAD_HANDLES: Arc<Mutex<HashMap<i64, thread::JoinHandle<Value>>>> =
        Arc::new(Mutex::new(HashMap::new()));
    static ref THREAD_RESULTS: Arc<Mutex<HashMap<i64, Value>>> =
        Arc::new(Mutex::new(HashMap::new()));
    static ref CHANNELS: Arc<Mutex<HashMap<i64, (Sender<Value>, Arc<Mutex<Receiver<Value>>>)>>> =
        Arc::new(Mutex::new(HashMap::new()));
    static ref NEXT_HANDLE_ID: Arc<Mutex<i64>> = Arc::new(Mutex::new(1));
    static ref NEXT_CHANNEL_ID: Arc<Mutex<i64>> = Arc::new(Mutex::new(1));
}

// ============================================================================
// Thread Operations
// ============================================================================

/// Get number of available CPU cores
pub fn rt_thread_available_parallelism(_args: &[Value]) -> Result<Value, CompileError> {
    let registry = get_concurrent_registry();
    if registry.backend() != ConcurrentBackend::PureStd {
        return registry.thread.thread_available_parallelism().map(|n| Value::Int(n as i64));
    }

    let cores = thread::available_parallelism().map(|n| n.get()).unwrap_or(1);
    Ok(Value::Int(cores as i64))
}

/// Sleep current thread for specified milliseconds
pub fn rt_thread_sleep(args: &[Value]) -> Result<Value, CompileError> {
    let registry = get_concurrent_registry();
    if registry.backend() != ConcurrentBackend::PureStd {
        let millis = match &args[0] {
            Value::Int(n) => *n as u64,
            _ => {
                return Err(CompileError::Runtime(
                    "rt_thread_sleep expects integer milliseconds".to_string(),
                ))
            }
        };
        return registry.thread.thread_sleep(millis).map(|_| Value::Nil);
    }

    if args.len() != 1 {
        return Err(CompileError::Runtime(
            "rt_thread_sleep expects 1 argument (millis)".to_string(),
        ));
    }

    let millis = match &args[0] {
        Value::Int(n) => *n as u64,
        _ => {
            return Err(CompileError::Runtime(
                "rt_thread_sleep expects integer milliseconds".to_string(),
            ))
        }
    };

    thread::sleep(Duration::from_millis(millis));
    Ok(Value::Nil)
}

/// Yield current thread to scheduler
pub fn rt_thread_yield(_args: &[Value]) -> Result<Value, CompileError> {
    let registry = get_concurrent_registry();
    if registry.backend() != ConcurrentBackend::PureStd {
        return registry.thread.thread_yield_now().map(|_| Value::Nil);
    }

    thread::yield_now();
    Ok(Value::Nil)
}

/// Spawn isolated thread with closure execution
///
/// Accepts a closure and optional arguments. Executes the closure with full
/// interpreter context. In PureStd mode, runs synchronously. In Native mode,
/// could be extended to spawn real OS threads.
pub fn rt_thread_spawn_isolated_with_context(
    args: &[Value],
    _env: &mut Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    if args.is_empty() {
        return Err(CompileError::Runtime(
            "rt_thread_spawn_isolated expects at least 1 argument (closure, ...args)".to_string(),
        ));
    }

    // Extract the closure
    let (params, body, captured_env) = match &args[0] {
        Value::Lambda { params, body, env } => (params.clone(), body.clone(), env.clone()),
        _ => {
            return Err(CompileError::Runtime(
                "rt_thread_spawn_isolated expects first argument to be a closure".to_string(),
            ))
        }
    };

    // Generate handle ID
    let mut next_id = NEXT_HANDLE_ID.lock().unwrap();
    let handle_id = *next_id;
    *next_id += 1;
    drop(next_id);

    // Execute the closure with bound parameters
    let mut local_env = captured_env.clone();

    // Bind any additional args to params
    for (i, param) in params.iter().enumerate() {
        if let Some(arg) = args.get(i + 1) {
            local_env.insert(param.clone(), arg.clone());
        }
    }

    // Evaluate the body expression
    let body_value =
        evaluate_expr(&body, &mut local_env, functions, classes, enums, impl_methods)
            .unwrap_or(Value::Nil);

    // If it's a BlockClosure, execute it; otherwise use the value directly
    let result = match &body_value {
        Value::BlockClosure { .. } => exec_block_value(
            body_value.clone(),
            &mut local_env,
            functions,
            classes,
            enums,
            impl_methods,
        )
        .unwrap_or(Value::Nil),
        _ => body_value,
    };

    // Store the result
    THREAD_RESULTS.lock().unwrap().insert(handle_id, result);
    Ok(Value::Int(handle_id))
}

/// Spawn isolated thread with 2 arguments and interpreter context
///
/// Executes the closure synchronously with full interpreter context.
/// The closure receives two data arguments and can perform any operation.
pub fn rt_thread_spawn_isolated2_with_context(
    args: &[Value],
    _env: &mut Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    if args.len() != 3 {
        return Err(CompileError::Runtime(
            "rt_thread_spawn_isolated2 expects 3 arguments (closure, data1, data2)".to_string(),
        ));
    }

    // Extract the closure
    let (params, body, captured_env) = match &args[0] {
        Value::Lambda { params, body, env } => (params.clone(), body.clone(), env.clone()),
        _ => {
            return Err(CompileError::Runtime(
                "rt_thread_spawn_isolated2 expects first argument to be a closure".to_string(),
            ))
        }
    };

    // Clone data for thread isolation
    let data1 = args[1].clone();
    let data2 = args[2].clone();

    // Generate handle ID
    let mut next_id = NEXT_HANDLE_ID.lock().unwrap();
    let handle_id = *next_id;
    *next_id += 1;
    drop(next_id);

    // Execute the closure with bound parameters
    let mut local_env = captured_env.clone();

    // Bind parameters to data arguments
    if params.len() >= 1 {
        local_env.insert(params[0].clone(), data1);
    }
    if params.len() >= 2 {
        local_env.insert(params[1].clone(), data2);
    }

    // First evaluate the body expression to get a potentially BlockClosure value
    let body_value =
        evaluate_expr(&body, &mut local_env, functions, classes, enums, impl_methods).unwrap_or(Value::Nil);

    // If it's a BlockClosure, execute it; otherwise use the value directly
    let result = match &body_value {
        Value::BlockClosure { .. } => exec_block_value(
            body_value.clone(),
            &mut local_env,
            functions,
            classes,
            enums,
            impl_methods,
        )
        .unwrap_or(Value::Nil),
        _ => body_value,
    };

    // Store the result
    THREAD_RESULTS.lock().unwrap().insert(handle_id, result);
    Ok(Value::Int(handle_id))
}

/// Join a thread and get its result
pub fn rt_thread_join(args: &[Value]) -> Result<Value, CompileError> {
    let registry = get_concurrent_registry();
    if registry.backend() != ConcurrentBackend::PureStd {
        let handle_id = match &args[0] {
            Value::Int(id) => *id,
            _ => {
                return Err(CompileError::Runtime(
                    "rt_thread_join expects integer handle".to_string(),
                ))
            }
        };
        return registry.thread.thread_join(handle_id);
    }

    if args.len() != 1 {
        return Err(CompileError::Runtime(
            "rt_thread_join expects 1 argument (handle)".to_string(),
        ));
    }

    let handle_id = match &args[0] {
        Value::Int(id) => *id,
        _ => {
            return Err(CompileError::Runtime(
                "rt_thread_join expects integer handle".to_string(),
            ))
        }
    };

    // Retrieve stored result
    let result = THREAD_RESULTS.lock().unwrap().remove(&handle_id).unwrap_or(Value::Nil);

    Ok(result)
}

/// Check if thread is done
pub fn rt_thread_is_done(args: &[Value]) -> Result<Value, CompileError> {
    let registry = get_concurrent_registry();
    if registry.backend() != ConcurrentBackend::PureStd {
        let handle = match &args[0] {
            Value::Int(id) => *id,
            _ => {
                return Err(CompileError::Runtime(
                    "rt_thread_is_done expects integer handle".to_string(),
                ))
            }
        };
        return registry.thread.thread_is_done(handle).map(|b| Value::Int(if b { 1 } else { 0 }));
    }

    // For now, always return true (thread is done)
    Ok(Value::Int(1))
}

/// Get thread ID
pub fn rt_thread_id(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 1 {
        return Err(CompileError::Runtime(
            "rt_thread_id expects 1 argument (handle)".to_string(),
        ));
    }

    match &args[0] {
        Value::Int(handle) => Ok(Value::Int(*handle)),
        _ => Err(CompileError::Runtime("rt_thread_id expects integer handle".to_string())),
    }
}

/// Free thread handle
pub fn rt_thread_free(args: &[Value]) -> Result<Value, CompileError> {
    let registry = get_concurrent_registry();
    if registry.backend() != ConcurrentBackend::PureStd {
        let handle = match &args[0] {
            Value::Int(id) => *id,
            _ => {
                return Err(CompileError::Runtime(
                    "rt_thread_free expects integer handle".to_string(),
                ))
            }
        };
        return registry.thread.thread_free(handle).map(|_| Value::Nil);
    }

    Ok(Value::Nil)
}

// ============================================================================
// Channel Operations
// ============================================================================

/// Create a new channel
pub fn rt_channel_new(_args: &[Value]) -> Result<Value, CompileError> {
    let registry = get_concurrent_registry();
    if registry.backend() != ConcurrentBackend::PureStd {
        return registry.channel.channel_new().map(|h| Value::Int(h));
    }

    let (tx, rx) = channel::<Value>();

    let mut channels = CHANNELS.lock().unwrap();
    let mut next_id = NEXT_CHANNEL_ID.lock().unwrap();
    let channel_id = *next_id;
    *next_id += 1;

    channels.insert(channel_id, (tx, Arc::new(Mutex::new(rx))));

    Ok(Value::Int(channel_id))
}

/// Send value to channel
pub fn rt_channel_send(args: &[Value]) -> Result<Value, CompileError> {
    let registry = get_concurrent_registry();
    if registry.backend() != ConcurrentBackend::PureStd {
        let channel_id = match &args[0] {
            Value::Int(id) => *id,
            _ => {
                return Err(CompileError::Runtime(
                    "rt_channel_send expects integer channel_id".to_string(),
                ))
            }
        };
        let value = args[1].clone();
        return registry.channel.channel_send(channel_id, value).map(|_| Value::Nil);
    }

    if args.len() != 2 {
        return Err(CompileError::Runtime(
            "rt_channel_send expects 2 arguments (channel_id, value)".to_string(),
        ));
    }

    let channel_id = match &args[0] {
        Value::Int(id) => *id,
        _ => {
            return Err(CompileError::Runtime(
                "rt_channel_send expects integer channel_id".to_string(),
            ))
        }
    };

    let channels = CHANNELS.lock().unwrap();
    if let Some((tx, _)) = channels.get(&channel_id) {
        let value = args[1].clone();
        tx.send(value)
            .map_err(|_| CompileError::Runtime("Failed to send to channel".to_string()))?;
        Ok(Value::Nil)
    } else {
        Err(CompileError::Runtime(format!("Channel {} not found", channel_id)))
    }
}

/// Try to receive value from channel (non-blocking)
pub fn rt_channel_try_recv(args: &[Value]) -> Result<Value, CompileError> {
    let registry = get_concurrent_registry();
    if registry.backend() != ConcurrentBackend::PureStd {
        let channel_id = match &args[0] {
            Value::Int(id) => *id,
            _ => {
                return Err(CompileError::Runtime(
                    "rt_channel_try_recv expects integer channel_id".to_string(),
                ))
            }
        };
        return registry.channel.channel_try_recv(channel_id);
    }

    if args.len() != 1 {
        return Err(CompileError::Runtime(
            "rt_channel_try_recv expects 1 argument (channel_id)".to_string(),
        ));
    }

    let channel_id = match &args[0] {
        Value::Int(id) => *id,
        _ => {
            return Err(CompileError::Runtime(
                "rt_channel_try_recv expects integer channel_id".to_string(),
            ))
        }
    };

    let channels = CHANNELS.lock().unwrap();
    if let Some((_, rx)) = channels.get(&channel_id) {
        let rx = rx.lock().unwrap();
        match rx.try_recv() {
            Ok(value) => Ok(value),
            Err(_) => Ok(Value::Nil), // Return nil if no value available
        }
    } else {
        Err(CompileError::Runtime(format!("Channel {} not found", channel_id)))
    }
}

/// Blocking receive from channel
pub fn rt_channel_recv(args: &[Value]) -> Result<Value, CompileError> {
    let registry = get_concurrent_registry();
    if registry.backend() != ConcurrentBackend::PureStd {
        let channel_id = match &args[0] {
            Value::Int(id) => *id,
            _ => {
                return Err(CompileError::Runtime(
                    "rt_channel_recv expects integer channel_id".to_string(),
                ))
            }
        };
        return registry.channel.channel_recv(channel_id);
    }

    if args.len() != 1 {
        return Err(CompileError::Runtime(
            "rt_channel_recv expects 1 argument (channel_id)".to_string(),
        ));
    }

    let channel_id = match &args[0] {
        Value::Int(id) => *id,
        _ => {
            return Err(CompileError::Runtime(
                "rt_channel_recv expects integer channel_id".to_string(),
            ))
        }
    };

    let channels = CHANNELS.lock().unwrap();
    if let Some((_, rx)) = channels.get(&channel_id) {
        let rx_clone = rx.clone();
        drop(channels); // Release lock before blocking

        let rx = rx_clone.lock().unwrap();
        match rx.recv() {
            Ok(value) => Ok(value),
            Err(_) => Ok(Value::Nil),
        }
    } else {
        Err(CompileError::Runtime(format!("Channel {} not found", channel_id)))
    }
}

/// Close a channel
pub fn rt_channel_close(args: &[Value]) -> Result<Value, CompileError> {
    let registry = get_concurrent_registry();
    if registry.backend() != ConcurrentBackend::PureStd {
        let channel_id = match &args[0] {
            Value::Int(id) => *id,
            _ => {
                return Err(CompileError::Runtime(
                    "rt_channel_close expects integer channel_id".to_string(),
                ))
            }
        };
        return registry.channel.channel_close(channel_id).map(|_| Value::Nil);
    }

    if args.len() != 1 {
        return Err(CompileError::Runtime(
            "rt_channel_close expects 1 argument (channel_id)".to_string(),
        ));
    }

    let channel_id = match &args[0] {
        Value::Int(id) => *id,
        _ => {
            return Err(CompileError::Runtime(
                "rt_channel_close expects integer channel_id".to_string(),
            ))
        }
    };

    let mut channels = CHANNELS.lock().unwrap();
    channels.remove(&channel_id);

    Ok(Value::Nil)
}

/// Check if channel is closed
pub fn rt_channel_is_closed(args: &[Value]) -> Result<Value, CompileError> {
    let registry = get_concurrent_registry();
    if registry.backend() != ConcurrentBackend::PureStd {
        let channel_id = match &args[0] {
            Value::Int(id) => *id,
            _ => {
                return Err(CompileError::Runtime(
                    "rt_channel_is_closed expects integer channel_id".to_string(),
                ))
            }
        };
        return registry.channel.channel_is_closed(channel_id).map(|b| Value::Int(if b { 1 } else { 0 }));
    }

    if args.len() != 1 {
        return Err(CompileError::Runtime(
            "rt_channel_is_closed expects 1 argument (channel_id)".to_string(),
        ));
    }

    let channel_id = match &args[0] {
        Value::Int(id) => *id,
        _ => {
            return Err(CompileError::Runtime(
                "rt_channel_is_closed expects integer channel_id".to_string(),
            ))
        }
    };

    let channels = CHANNELS.lock().unwrap();
    let is_closed = !channels.contains_key(&channel_id);

    Ok(Value::Int(if is_closed { 1 } else { 0 }))
}

// ============================================================================
// Backend Configuration
// ============================================================================

/// Set the concurrent backend ("pure_std" or "native")
///
/// Switches the concurrent provider registry to use the specified backend.
/// This affects all subsequent concurrent operations (maps, channels, threads, etc.).
pub fn rt_set_concurrent_backend(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 1 {
        return Err(CompileError::Runtime(
            "rt_set_concurrent_backend expects 1 argument (backend_name: text)".to_string(),
        ));
    }

    let name = match &args[0] {
        Value::Str(s) => s.clone(),
        _ => {
            return Err(CompileError::Runtime(
                "rt_set_concurrent_backend expects a string argument".to_string(),
            ))
        }
    };

    let backend = ConcurrentBackend::parse(&name).map_err(|e| CompileError::Runtime(e))?;
    set_concurrent_registry(ConcurrentProviderRegistry::new(backend));
    Ok(Value::Nil)
}

/// Get the current concurrent backend name
pub fn rt_get_concurrent_backend(_args: &[Value]) -> Result<Value, CompileError> {
    let registry = get_concurrent_registry();
    let name = match registry.backend() {
        ConcurrentBackend::PureStd => "pure_std",
        ConcurrentBackend::Native => "native",
    };
    Ok(Value::Str(name.to_string()))
}
