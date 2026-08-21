# Unsafe block expression binding parser gap

Status: Open

The supported expression form

```simple
val handle = unsafe(capabilities: [ffi]):
    spl_mutex_create()
```

is rejected by the current deployed parser at the block colon. This prevents a
zero-overhead expression-scoped FFI boundary from binding its validated raw
result directly. The temporary migration form declares a typed local and
assigns it inside the lexical unsafe block. The optimizer must prove the initial
zero store dead before this workaround is accepted for a measured hot path.

Required fix: parse `unsafe(...)` block expressions wherever an ordinary value
expression is accepted, preserve their capability set in HIR, and add
interpreter/JIT/native parity plus generated-code evidence that the block itself
has no runtime cost.
