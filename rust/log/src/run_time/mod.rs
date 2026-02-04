//! Runtime logging for the Simple language interpreter and compiled code.
//!
//! This module provides structured logging for runtime events:
//! - Function calls and returns
//! - Memory allocation and GC
//! - Actor/async operations
//! - Value operations
//! - I/O operations
//!
//! # Usage
//!
//! ```ignore
//! use simple_log::run_time;
//!
//! // Log function execution
//! run_time::call("main", &["arg1", "arg2"]);
//! run_time::ret("main", "42");
//!
//! // Log memory events
//! run_time::alloc("Object", 256);
//! run_time::gc_start();
//! run_time::gc_end(100, 50);
//!
//! // Log actor events
//! run_time::actor_spawn("MyActor", 1);
//! run_time::actor_send(1, 2, "message");
//! ```
//!
//! # Filtering
//!
//! Use `SIMPLE_LOG` env var to filter:
//! - `SIMPLE_LOG=simple_log::run_time=debug` - all runtime logs
//! - `SIMPLE_LOG=simple_log::run_time::gc=trace` - GC only
//! - `SIMPLE_LOG=simple_log::run_time::actor=debug` - actors only

use tracing::{debug, error, info, span, trace, Level};

// =============================================================================
// Function Execution
// =============================================================================

/// Log a function call.
#[inline]
pub fn call(name: &str, args: &[&str]) {
    debug!(
        target: "simple_log::run_time::exec",
        name = name,
        args = ?args,
        "call"
    );
}

/// Log a function return.
#[inline]
pub fn ret(name: &str, value: &str) {
    debug!(
        target: "simple_log::run_time::exec",
        name = name,
        value = value,
        "return"
    );
}

/// Log entering a code block.
#[inline]
pub fn block_enter(kind: &str) {
    trace!(
        target: "simple_log::run_time::exec",
        kind = kind,
        "block enter"
    );
}

/// Log exiting a code block.
#[inline]
pub fn block_exit(kind: &str) {
    trace!(
        target: "simple_log::run_time::exec",
        kind = kind,
        "block exit"
    );
}

/// Log a runtime error.
#[inline]
pub fn runtime_error(message: &str, location: &str) {
    error!(
        target: "simple_log::run_time::exec",
        message = message,
        location = location,
        "runtime error"
    );
}

/// Log a panic/unrecoverable error.
#[inline]
pub fn panic(message: &str, location: &str) {
    error!(
        target: "simple_log::run_time::exec",
        message = message,
        location = location,
        "PANIC"
    );
}

// =============================================================================
// Memory and GC
// =============================================================================

/// Log a memory allocation.
#[inline]
pub fn alloc(type_name: &str, size: usize) {
    trace!(
        target: "simple_log::run_time::gc",
        type_name = type_name,
        size = size,
        "alloc"
    );
}

/// Log a memory deallocation.
#[inline]
pub fn dealloc(type_name: &str, size: usize) {
    trace!(
        target: "simple_log::run_time::gc",
        type_name = type_name,
        size = size,
        "dealloc"
    );
}

/// Log GC cycle start.
#[inline]
pub fn gc_start() {
    info!(
        target: "simple_log::run_time::gc",
        "gc start"
    );
}

/// Log GC cycle end.
#[inline]
pub fn gc_end(collected: usize, remaining: usize) {
    info!(
        target: "simple_log::run_time::gc",
        collected = collected,
        remaining = remaining,
        "gc end"
    );
}

/// Log GC marking phase.
#[inline]
pub fn gc_mark(objects_marked: usize) {
    debug!(
        target: "simple_log::run_time::gc",
        objects_marked = objects_marked,
        "gc mark"
    );
}

/// Log GC sweep phase.
#[inline]
pub fn gc_sweep(objects_freed: usize, bytes_freed: usize) {
    debug!(
        target: "simple_log::run_time::gc",
        objects_freed = objects_freed,
        bytes_freed = bytes_freed,
        "gc sweep"
    );
}

/// Log heap statistics.
#[inline]
pub fn heap_stats(total: usize, used: usize, free: usize) {
    debug!(
        target: "simple_log::run_time::gc",
        total = total,
        used = used,
        free = free,
        "heap stats"
    );
}

// =============================================================================
// Actors and Async
// =============================================================================

/// Log actor spawn.
#[inline]
pub fn actor_spawn(name: &str, id: u64) {
    info!(
        target: "simple_log::run_time::actor",
        name = name,
        id = id,
        "actor spawn"
    );
}

/// Log actor termination.
#[inline]
pub fn actor_terminate(id: u64, reason: &str) {
    info!(
        target: "simple_log::run_time::actor",
        id = id,
        reason = reason,
        "actor terminate"
    );
}

/// Log message send between actors.
#[inline]
pub fn actor_send(from: u64, to: u64, message_type: &str) {
    debug!(
        target: "simple_log::run_time::actor",
        from = from,
        to = to,
        message_type = message_type,
        "actor send"
    );
}

/// Log message receive by actor.
#[inline]
pub fn actor_recv(id: u64, message_type: &str) {
    debug!(
        target: "simple_log::run_time::actor",
        id = id,
        message_type = message_type,
        "actor recv"
    );
}

/// Log async task spawn.
#[inline]
pub fn async_spawn(task_id: u64, name: &str) {
    debug!(
        target: "simple_log::run_time::async",
        task_id = task_id,
        name = name,
        "async spawn"
    );
}

/// Log async task completion.
#[inline]
pub fn async_complete(task_id: u64, name: &str) {
    debug!(
        target: "simple_log::run_time::async",
        task_id = task_id,
        name = name,
        "async complete"
    );
}

/// Log await point.
#[inline]
pub fn await_start(task_id: u64, awaiting: &str) {
    trace!(
        target: "simple_log::run_time::async",
        task_id = task_id,
        awaiting = awaiting,
        "await start"
    );
}

/// Log await completion.
#[inline]
pub fn await_end(task_id: u64, awaiting: &str) {
    trace!(
        target: "simple_log::run_time::async",
        task_id = task_id,
        awaiting = awaiting,
        "await end"
    );
}

// =============================================================================
// I/O Operations
// =============================================================================

/// Log file open.
#[inline]
pub fn file_open(path: &str, mode: &str) {
    debug!(
        target: "simple_log::run_time::io",
        path = path,
        mode = mode,
        "file open"
    );
}

/// Log file close.
#[inline]
pub fn file_close(path: &str) {
    debug!(
        target: "simple_log::run_time::io",
        path = path,
        "file close"
    );
}

/// Log file read.
#[inline]
pub fn file_read(path: &str, bytes: usize) {
    trace!(
        target: "simple_log::run_time::io",
        path = path,
        bytes = bytes,
        "file read"
    );
}

/// Log file write.
#[inline]
pub fn file_write(path: &str, bytes: usize) {
    trace!(
        target: "simple_log::run_time::io",
        path = path,
        bytes = bytes,
        "file write"
    );
}

/// Log network connection.
#[inline]
pub fn net_connect(addr: &str, protocol: &str) {
    debug!(
        target: "simple_log::run_time::io",
        addr = addr,
        protocol = protocol,
        "net connect"
    );
}

/// Log network disconnect.
#[inline]
pub fn net_disconnect(addr: &str) {
    debug!(
        target: "simple_log::run_time::io",
        addr = addr,
        "net disconnect"
    );
}

/// Log I/O error.
#[inline]
pub fn io_error(operation: &str, error: &str) {
    error!(
        target: "simple_log::run_time::io",
        operation = operation,
        error = error,
        "io error"
    );
}

// =============================================================================
// Value Operations
// =============================================================================

/// Log value creation.
#[inline]
pub fn value_create(type_name: &str, value: &str) {
    trace!(
        target: "simple_log::run_time::value",
        type_name = type_name,
        value = value,
        "value create"
    );
}

/// Log value conversion.
#[inline]
pub fn value_convert(from_type: &str, to_type: &str) {
    trace!(
        target: "simple_log::run_time::value",
        from_type = from_type,
        to_type = to_type,
        "value convert"
    );
}

/// Log method dispatch.
#[inline]
pub fn method_dispatch(receiver_type: &str, method: &str) {
    trace!(
        target: "simple_log::run_time::value",
        receiver_type = receiver_type,
        method = method,
        "method dispatch"
    );
}

// =============================================================================
// Spans for Tracing
// =============================================================================

/// Create a span for a function call.
#[inline]
pub fn call_span(name: &str) -> tracing::Span {
    span!(Level::DEBUG, "call", name = name)
}

/// Create a span for GC cycle.
#[inline]
pub fn gc_span() -> tracing::Span {
    span!(Level::INFO, "gc_cycle")
}

/// Create a span for an actor's lifetime.
#[inline]
pub fn actor_span(name: &str, id: u64) -> tracing::Span {
    span!(Level::INFO, "actor", name = name, id = id)
}

/// Create a span for an async task.
#[inline]
pub fn async_span(task_id: u64, name: &str) -> tracing::Span {
    span!(Level::DEBUG, "async_task", task_id = task_id, name = name)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_exec_logging() {
        call("main", &["arg1", "arg2"]);
        ret("main", "42");
        block_enter("if");
        block_exit("if");
        runtime_error("division by zero", "main:10");
    }

    #[test]
    fn test_gc_logging() {
        alloc("String", 256);
        dealloc("String", 256);
        gc_start();
        gc_mark(100);
        gc_sweep(50, 4096);
        gc_end(50, 100);
        heap_stats(1024 * 1024, 512 * 1024, 512 * 1024);
    }

    #[test]
    fn test_actor_logging() {
        actor_spawn("MyActor", 1);
        actor_send(1, 2, "Ping");
        actor_recv(2, "Ping");
        actor_terminate(1, "normal");
    }

    #[test]
    fn test_async_logging() {
        async_spawn(1, "fetch_data");
        await_start(1, "http_request");
        await_end(1, "http_request");
        async_complete(1, "fetch_data");
    }

    #[test]
    fn test_io_logging() {
        file_open("/tmp/test.txt", "r");
        file_read("/tmp/test.txt", 1024);
        file_write("/tmp/test.txt", 512);
        file_close("/tmp/test.txt");
        net_connect("127.0.0.1:8080", "tcp");
        net_disconnect("127.0.0.1:8080");
        io_error("read", "connection reset");
    }

    #[test]
    fn test_value_logging() {
        value_create("Int", "42");
        value_convert("Int", "Float");
        method_dispatch("String", "len");
    }
}
