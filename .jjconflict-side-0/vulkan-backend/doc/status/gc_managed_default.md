# Feature #24: GC-Managed Memory

**Status**: Implemented
**Difficulty**: 5
**Importance**: 5

## Summary

Garbage-collected memory management is the default for heap allocations. The runtime includes a working GC with logging support.

## Features

- [x] GcRuntime implementation (wraps Abfall)
- [x] GcAllocator trait (common crate)
- [x] Allocation tracking
- [x] Manual collection trigger
- [x] Verbose GC logging with structured events
- [x] GcLogEvent types: Allocation, CollectionStart, CollectionEnd
- [x] No-GC mode for performance testing
- [x] CLI `--gc-log` flag for runtime logging
- [x] Post-run automatic collection

## Tests

### Runtime Tests (src/runtime/tests/)
- `gc_allocator::allocator_contract_allocates_and_collects`
- `gc_logging::verbose_logging_emits_collection_markers`
- `gc_logging::structured_events_are_emitted`
- `no_gc_allocator::no_gc_allocator_allocates_without_tracing`

### Runner Tests (src/driver/tests/)
- `runner_emits_gc_logs_in_verbose_mode`
- `runner_supports_gc_off_mode`
- `cli_flag_emits_gc_logs`

## Usage

```rust
// With GC logging
let runner = Runner::with_gc_runtime(GcRuntime::with_logger(|event| {
    println!("{}", event);
}));

// Without GC
let runner = Runner::new_no_gc();
```

```bash
# CLI with GC logging
simple-driver run main.spl --gc-log
```

## Implementation

- **common/gc.rs**: `GcAllocator` trait defining allocator contract
- **runtime/gc/mod.rs**: `GcRuntime`, `GcLogEvent`, `GcLogEventKind`
- **driver**: Integration with Runner, CLI flag support

## Log Format

```
gc:start reason=post-run
gc:end reason=post-run freed=0 retained=0
```

## Future Work

- Route actual language allocations through GC (currently stub codegen)
- Generational collection
- Concurrent collection
