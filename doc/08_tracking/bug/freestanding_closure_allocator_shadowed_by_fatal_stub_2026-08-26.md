# Freestanding closure allocator shadowed by fatal boot stub

Status: fixed in source; fresh guest capture pending.

The x86_64 boot support defined a strong `S1(rt_closure_new)` fatal stub even
when the selected runtime bundle supplied the real closure allocator and the
linked image contained real closure accessors. Browser Demo spawning therefore
halted at its first zero-capture closure allocation.

The boot stub definition is removed. `rt_closure_new` must now resolve from the
selected runtime bundle, and no-stub linking fails closed if that provider is
absent. This preserves one coherent closure layout and real allocation policy.
