# Feature: GC-Managed Default (Feature #24)

- **Importance**: 5/5
- **Difficulty**: 5/5
- **Status**: COMPLETED

## Plan
- Define GC handle/allocator traits in `src/common/`.
- Adapt `runtime::gc::GcRuntime` to implement the allocator contract and expose options/logging.
- Teach compiler codegen to route default heap allocations through the GC allocator; pointer kinds opt out.
- Expose CLI flags/env for GC tuning; keep logging via `--gc-log`.

## Current Work
- `runtime::gc::GcRuntime` wraps Abfall with structured `GcLogEvent` markers and implements `common::gc::GcAllocator`; CLI flag `--gc-log` surfaces events.
- Driver system tests assert GC logging hooks (runner logger + CLI flag). Compiler will route real allocations once codegen expands beyond the stub.

## References
- Plan: `plans/13_type_inference_generics_gc.md`
- Research: `research/type_inference_generics_gc.md`
