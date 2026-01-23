// Concurrency Operations (Threads and Channels)
//
// Thread operations for isolated thread spawning and management
// Channel operations for thread communication

use crate::error::CompileError;
use crate::interpreter::evaluate_expr;
use crate::value::{Env, Value};
use simple_parser::ast::{Argument, ClassDef, EnumDef, Expr, FunctionDef};
use std::sync::mpsc::{channel, Sender, Receiver};
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::Duration;
use std::collections::HashMap;

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
    let cores = thread::available_parallelism().map(|n| n.get()).unwrap_or(1);
    Ok(Value::Int(cores as i64))
}

/// Sleep current thread for specified milliseconds
pub fn rt_thread_sleep(args: &[Value]) -> Result<Value, CompileError> {
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
    thread::yield_now();
    Ok(Value::Nil)
}

/// Spawn isolated thread (simplified version - just returns a dummy handle for now)
pub fn rt_thread_spawn_isolated(args: &[Value]) -> Result<Value, CompileError> {
    // For now, return a dummy handle ID
    // Full implementation would need closure support in interpreter
    let mut next_id = NEXT_HANDLE_ID.lock().unwrap();
    let handle_id = *next_id;
    *next_id += 1;

    // Just return the handle ID - actual thread spawning would require
    // evaluating the closure argument which needs more interpreter integration
    Ok(Value::Int(handle_id))
}

/// Spawn isolated thread with 2 arguments (basic version without context)
///
/// This version does not execute closures - use rt_thread_spawn_isolated2_with_context instead.
pub fn rt_thread_spawn_isolated2(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 3 {
        return Err(CompileError::Runtime(
            "rt_thread_spawn_isolated2 expects 3 arguments (closure, data1, data2)".to_string(),
        ));
    }

    // Generate handle ID
    let mut next_id = NEXT_HANDLE_ID.lock().unwrap();
    let handle_id = *next_id;
    *next_id += 1;
    drop(next_id);

    // Without context, we can only store nil as result
    THREAD_RESULTS.lock().unwrap().insert(handle_id, Value::Nil);

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

    // Execute the closure body
    let result = evaluate_expr(&body, &mut local_env, functions, classes, enums, impl_methods)
        .unwrap_or(Value::Nil);

    // Store the result
    THREAD_RESULTS.lock().unwrap().insert(handle_id, result);

    Ok(Value::Int(handle_id))
}

/// Join a thread and get its result
pub fn rt_thread_join(args: &[Value]) -> Result<Value, CompileError> {
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
    Ok(Value::Nil)
}

// ============================================================================
// Channel Operations
// ============================================================================

/// Create a new channel
pub fn rt_channel_new(_args: &[Value]) -> Result<Value, CompileError> {
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
