# Mimalloc TLS unset-slot regression

Executable scenario: [`test/01_unit/lib/alloc/mimalloc_tls_unset_slot_spec.spl`](../../../../../test/01_unit/lib/alloc/mimalloc_tls_unset_slot_spec.spl).

The self-hosted integer TLS runtime returns `0` for an unset thread-local value. The scenario creates a
fresh TLS handle, observes that value, and then initializes the `nogc_sync_mut`,
`nogc_async_mut`, and `gc_async_mut` mimalloc heap families. Each registered
heap ID must differ from the unset value. `gc_sync_mut` re-exports the
`gc_async_mut` implementation and needs no separate state test.

This guards against a new thread looking up or destroying the first heap
registered by another thread. It checks the slot-ID invariant; a native
cross-thread execution check remains pending a qualified self-hosted producer.
The older Rust `RuntimeValue` TLS ABI yields tagged NIL instead; a failure on
that provider must not be counted as proof of the integer contract.
