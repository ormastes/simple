# MIR actor send status ABI

The raw MIR runtime bridge owns conversion between lowered actor operands and
the registered runtime ABI. `rt_actor_send(i64, i64)` returns void;
`rt_actor_try_send(i64, i64)` returns an i64 acceptance status. A bridge returning
i64 must call the latter. The runtime registry and runtime actor implementation
agree on these signatures.

The pure `std.actor` scheduler is the preferred public actor surface. It cannot
replace this internal bridge directly: the bridge receives lowered raw runtime
handles, while the scheduler owns typed actor references. This repair keeps the
existing unsafe(ffi) capability annotation and adds no conversion or allocation.

Legacy generic actor hooks reject calls with E-SFFI-ACTOR-LEGACY-ABI rather than
passing Any across the raw boundary. The source contract must follow the current
`mir_interp_runtime.spl` owner and the facade's export, while retaining negative
checks for invalid raw calls.

The retained LLVM seed backend still calls rt_actor_spawn with one operand,
although the registry requires handler and context. That separate defect keeps
the combined actor ABI source contract failing. This change does not qualify
the native backend or admit a rebuilt runtime.
