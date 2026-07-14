# SimpleOS optimizer passes tagged nil as `local_ids`

## Symptom

Filesystem `emit-llvm` reached HIR and MIR, then faulted at `local_count_index+0x29` while loading array length from offset 8. `CR2=0x8` proved the `[i64]` receiver was nil.

## Proven boundaries

Target disassembly proves `analyze_var_reassign_blocks` creates all six initial arrays with `rt_array_new(16)`; an empty array is not the nil sentinel. The count and alias update helpers previously allocated replacement arrays and tuples, so they were changed to mutate the persistent arrays in place. This removed a real allocation/nil propagation hazard but did not eliminate the live failure.

The current target contains no tuple get/set/new calls in those helpers. `local_ids` is stored once from the first `rt_array_new` return at analyzer stack slot `rsp+0x180`; generated code contains no later store to that slot. `rt_array_new` returns a tagged handle or raw zero, never tagged nil `3`.

## Current exact evidence

The caller-specific live marker prints `[var-reassign] count-increment=3` immediately before the fault. `local_alias_root` runs first and emits no invalid-handle marker. `local_count_increment` then reloads `local_ids` directly from `rsp+0x180`, receives `3`, and `local_count_index` faults on the unchecked offset-eight length load.

Routing typed `.len()` through `rt_array_len_safe` was rejected and reverted: it would hide the invalid producer and let optimizer analysis continue with false empty-state results. A QEMU hardware watchpoint set before the user CR3 became active did not bind; the run reproduced the same marker/fault without new evidence.

Next session must attach GDB only after the serial `[spawn] entering user` marker (when the user CR3 is active), break immediately after the `rsp+0x180` constructor store, and watch that address. Capture the first writing instruction or stack-pointer displacement. Do not re-add safe length, sentinel entries, tuple state, or heap growth.
