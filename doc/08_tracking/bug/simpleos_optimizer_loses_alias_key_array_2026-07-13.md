# SimpleOS optimizer passes tagged nil as `local_ids`

**Status:** OPEN — source fixed; SimpleOS target verification pending.

## Symptom

Filesystem `emit-llvm` reached HIR and MIR, then faulted at `local_count_index+0x29` while loading array length from offset 8. `CR2=0x8` proved the `[i64]` receiver was nil.

## Proven boundaries

Target disassembly proves `analyze_var_reassign_blocks` creates all six initial arrays with `rt_array_new(16)`; an empty array is not the nil sentinel. The count and alias update helpers previously allocated replacement arrays and tuples, so they were changed to mutate the persistent arrays in place. This removed a real allocation/nil propagation hazard but did not eliminate the live failure.

The current target contains no tuple get/set/new calls in those helpers. `local_ids` is stored once from the first `rt_array_new` return at analyzer stack slot `rsp+0x180`; generated code contains no later store to that slot. `rt_array_new` returns a tagged handle or raw zero, never tagged nil `3`.

## Current exact evidence

The final phase-checkpoint serial output contained only `[var-reassign] count-increment=3` before `local_count_index` faulted at `RIP 0x102a793f` (`CR2=0x8`). That text is a hard-coded low-positive branch label, not the numeric parameter. Caller-side checkpoint silence does not prove their branches were not taken because those diagnostics themselves route through fallible string allocation/output.

Routing typed `.len()` through `rt_array_len_safe` was rejected and reverted: it would hide the invalid producer and let optimizer analysis continue with false empty-state results. A QEMU hardware watchpoint set before the user CR3 became active did not bind; the run reproduced the same marker/fault without new evidence.

Two later GDB attempts reached the active user CR3, but execution breakpoints still did not trap reliably across the handoff. Static disassembly found a fixed analyzer stack, one constructor store for `local_ids`, balanced helper frames, and no callee-saved-register violation. The final ELF also proves the caller compares and reloads the same `rsp+0x298` slot into `RDI`, then the direct callee preserves that register through its low-value test and `local_count_index` call. All FAT Simple aliases match that ELF. The apparent call-boundary corruption is therefore contradicted by machine code.

Do not patch call lowering or spend another live cycle on watchpoints. Next session must capture the actual caller-slot and callee-entry values through a numeric/global diagnostic that cannot fail silently, then reconcile the serial sequence before changing an owner. Do not re-add safe length, sentinel entries, tuple state, heap growth, or string-only runtime probes.

## Source-fix evidence and target-verification gap

`5d614ae9904` removed the parallel `[i64]` owner state from
`analyze_var_reassign_blocks`: counts, borrowed locals, escaped locals, and
aliases are now keyed `Dict` values. This eliminates the replacement-array
alias path that could pass a nil `local_ids` receiver to `local_count_index`.
The existing regression assertion constructs 256 distinct local ids, assigns
each twice, and requires `reassignment_count == 256` with a safe SSA result.
It passed with `bin/simple test --no-session-daemon
test/01_unit/compiler/mir_opt/var_reassign_analysis_spec.spl` (20/20). The
runner reported its executed child as
`bin/release/aarch64-unknown-linux-gnu/simple`, the repository's pure-Simple
release runtime, after the bootstrap-seed driver emitted its warning.

There is no retained automated red-before result for the original SimpleOS
filesystem `emit-llvm` target, and this host-only unit run does not replace
that target proof. The historical serial fault remains the red evidence. Keep
this issue open until an admitted SimpleOS target runs the original path without
the `local_count_index` nil-receiver fault.

SOSIX compatibility: the change is internal to the MIR optimizer. The exported
`analyze_var_reassign_blocks` signature and the JIT specialization-provider
call path are unchanged; the focused test exercises that provider path.
