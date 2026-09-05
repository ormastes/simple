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

The gap is compilation-context dependent: direct checks of process-governor
and compiler-driver modules currently lower the same lexical block spelling as
a call to a missing function named `unsafe`. Those sites must temporarily use
function-level `@unsafe(... capabilities: [ffi])`, which widens authority but
does not add runtime work. The parser/lowering fix must make lexical blocks
portable across module families before these scopes can be narrowed.
