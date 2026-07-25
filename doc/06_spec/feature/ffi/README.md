# FFI Specifications

Mirrors: `test/feature/ffi/`
Generated: `doc/06_spec/app/compiler/feature/ffi/`

FFI (Foreign Function Interface) integration specs: syscall wrappers,
C interop, runtime extern declarations, and FFI boundary testing.

Note: ffi test files use non-standard naming (not `_spec.spl`).

## Test Files

| File | Purpose |
|------|---------|
| `ffi_hello_world.spl` | Basic FFI hello world demonstration |
| `syscalls_manual_verify.spl` | Manual syscall verification |
| `syscalls_test.spl` | Syscall integration tests |
