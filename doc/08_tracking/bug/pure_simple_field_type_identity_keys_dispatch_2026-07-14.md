# Pure-Simple Field Type Identity Can Misdispatch `keys`

## Status

Open compiler architecture debt. The bounded SimpleOS unblock is fixed at the
three statically declared `Dict` walks in async desugaring.

## Failure

When a field expression loses its declared `Dict<K, V>` type, global
same-name method resolution can bind `module.functions.keys()` to
`nogc_sync_mut.src.map.Map.keys`. Native execution then passes a tagged Dict
handle to a struct-layout method and segfaults.

The failure is reproducible while native-building the staged SimpleOS memory
leveling kernel. GDB reports `Map.keys -> desugar_async.desugar_module`.

## Required Owner Fix

Preserve module-qualified nominal identity and declared field type from HIR
through MIR. Field layout and method lookup must not use a bare struct name as
the authoritative identity when multiple imported modules define `Module`.
Erased receivers must not select user methods by global bare-name uniqueness.

The current async-desugar call sites use `std.alloc.sffi.rt_dict_keys` because
their receiver declarations are statically `Dict`; this does not change custom
`Map.keys` or `List.keys` dispatch.
