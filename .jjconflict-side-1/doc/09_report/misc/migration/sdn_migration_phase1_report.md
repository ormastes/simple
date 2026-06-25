# SDN Migration Phase 1 Report

## Current State

**Approach**: FFI wrapper around existing Rust library

```
Simple CLI (133 lines)
    ↓ calls
SDN FFI (274 lines Rust)
    ↓ calls
simple_sdn library (2591 lines Rust)
```

## Line Counts

| Component | Lines | Status |
|-----------|-------|--------|
| simple_sdn library | 2591 | Kept (Rust) |
| SDN FFI | 274 | New (Rust) |
| SDN Simple CLI | 133 | New (Simple) |
| **Total** | **2998** | +407 from original |

## Analysis

Current implementation does NOT reduce code size. It:
- Keeps entire SDN Rust library (2591 lines)
- Adds FFI layer (274 lines)
- Adds Simple CLI (133 lines)

**Net change**: +16% more code

## Options for Size Reduction

### Option A: Keep Current (Recommended for Now)
- SDN parsing is complex (error recovery, spans, tables)
- Rust implementation is well-tested (47 tests pass)
- Simple CLI provides good UX
- **Decision**: Accept current state, focus on other modules

### Option B: Full Simple Rewrite (Future)
- Rewrite parser in Simple
- Keep only lexer in Rust FFI
- Target: < 1000 lines Simple
- **Risk**: High effort, potential bugs

## Files Changed

| File | Lines | Type |
|------|-------|------|
| `src/rust/runtime/src/value/sdn_ffi.rs` | 274 | New |
| `src/app/sdn/main.spl` | 133 | New |

## Test Results

```
simple-sdn: 47 tests passed
simple-runtime sdn: 1 test passed
```

## Recommendation

**Accept current implementation**. SDN parser is complex and the Rust implementation works well. The Simple CLI provides value by making SDN tools accessible from Simple.

Focus effort on modules where Simple code will be genuinely shorter:
- Phase 3: DB modules (todo_db, feature_db, bug_db) - high potential
- Phase 2: Diagnostics - moderate potential

## Next Steps

1. Skip Phase 1.2-1.4 (parser rewrite not needed)
2. Proceed to Phase 2 (Diagnostics) or Phase 3 (DB modules)
