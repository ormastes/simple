# Bare `fn(args);` statement on a unit-returning fn → lenient_unresolved_global → link error

Date: 2026-09-25
Lane: lane-C1 aarch64 guest milestone (clang bring-up)
Severity: build-breaking; cost one full kernel rebuild cycle to diagnose.

## Symptom

A call to a `pub fn` defined EARLIER in the same module, written as a bare
expression-statement:

```spl
_vfs_state_mount_table_open_chain_probe_v1(path)   # unit-returning fn
```

fails at LINK time with:

```
undefined symbol: _vfs_state_mount_table_open_chain_probe_v1
note: ... reached the linker undeclared because HIR lowering resolved it to
nothing and the `lenient_types` fallback lowered it to a global.
```

The mangled definition (`src__os__...__vfs_state_mount_table_open_chain_probe_v1`)
exists in the same object; the call site instead references the RAW identifier
name with a C-style underscore prefix. The identical call written as a discard
assignment compiles and links correctly:

```spl
_ = vfs_state_mount_table_open_chain_probe_v1(path)   # resolves fine
```

Observed in the wild at
`src/os/services/vfs/vfs_boot_state.spl` (`vfs_state_positioned_open`'s
error path). Same-module, backward reference, `pub fn`, unit return.

## Suspected lowering gap

Statement-position calls of unit-returning fns take a lowering path that does
not consult the module's function table (unlike `_ = fn(...)` expression
position), so the identifier falls through to the `lenient_unresolved_global`
fallback. Whether the root cause is statement-vs-expression classification or
a missing entry in the unit-return special case is for the compiler lane to
pin.

## Workaround

Call unit-returning fns in expression position: `_ = fn(args)`.
