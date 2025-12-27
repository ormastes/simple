# FFI/ABI Interface (#1116-#1130)

Foreign Function Interface and Application Binary Interface.

## Features

| ID | Feature | Difficulty | Status | Impl |
|----|---------|------------|--------|------|
| #1116 | C ABI calling convention | 4 | ✅ | R |
| #1117 | Dynamic library loading | 4 | ✅ | R |
| #1118 | Type marshalling | 4 | ✅ | R |
| #1119 | Struct layout compatibility | 4 | ✅ | R |
| #1120 | Callback functions | 4 | ✅ | R |
| #1121 | String handling (C strings) | 3 | ✅ | R |
| #1122 | Array passing | 3 | ✅ | R |
| #1123 | Error handling across FFI | 4 | ✅ | R |
| #1124 | Thread safety for FFI calls | 4 | ✅ | R |
| #1125 | Memory ownership rules | 4 | ✅ | R |
| #1126 | Platform-specific ABIs | 4 | ✅ | R |
| #1127 | Varargs support | 3 | ✅ | R |
| #1128 | Opaque pointer types | 3 | ✅ | R |
| #1129 | FFI declaration syntax | 3 | ✅ | R |
| #1130 | Runtime library linking | 3 | ✅ | R |

## Summary

**Status:** 15/15 Complete (100%)

## FFI Syntax

```simple
# External function declaration
extern fn printf(format: *c_char, ...) -> i32

# Dynamic library loading
let lib = load_library("libfoo.so")
let func = lib.get_function("foo_init")

# Callback passing
fn callback(data: *void) -> i32:
    return 0

extern fn register_callback(cb: fn(*void) -> i32)
register_callback(callback)
```

## Documentation

- Archived in [feature_done_18.md](../done/feature_done_18.md)

## Implementation

- `src/compiler/src/interpreter_extern.rs`
- `src/native_loader/src/lib.rs`
