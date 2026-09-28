# x86_64 authenticated launch owner does not carry argv into execution

**Status:** source owner restored (work/restore-x86-64-launch-owner); guest
execution acceptance still open. **Inspected:** `origin/main` at `e2dab431827` on
2026-09-28. **Scope:** x86_64 SimpleOS authenticated filesystem execution and
terminal scheduler evidence.

`authenticated_fs_exec_submission_service_v1.spl` imports and calls
`x86_64_fs_exec_spawn_authenticated_with_launch_v1`, but
`x86_64_fs_exec_spawn.spl` does not define it. Adding a facade that validates
argv and then calls `fs_exec_adopt_authenticated_v1` would not complete the
route: that bridge passes no argv or envp to
`Scheduler.adopt_authenticated_executable_pid_v1`. The scheduler calls
`executable_prepare_image_v1`, which builds the user image with empty vectors,
and records adoption through `scheduler_execution_observe_adoption_v1` without
an observed command. The terminal
`scheduler_execution_compare_and_deliver_reaped_v2` requires a command
observation and exact path/argv match before issuing evidence.

The x86_64 launch owner must validate and retain one
`ExecutableLaunchArgumentsV1`, bind it to the admitted executable path and
recipe, pass its argv/envp into the mapped initial user stack, and record the
same owned launch in the scheduler observation before publication. The
one-shot executable authority, capability attenuation, child exit/reap, and
terminal evidence must remain one transaction. A source-only facade that
reports the caller's argv after a path-only adoption would make a false
execution claim.

Acceptance requires source-matched pure-Simple checks of the actual x86_64
closure and a guest execution proving argv/envp received by the child. Reject
invalid launch strings, recipe/path mismatch, inadequate caller capabilities,
stale/replayed authority, command mismatch, and incomplete reap without
terminal evidence. This remains a release blocker until those checks pass.

## 2026-09-28 update — source owner restored

Root cause: the whole chain was lost in stale snapshot `4edef8fab8` (first
landed as `06ca4a52099`). Restored minimally on current main:
`executable_prepare_image_with_launch_v1` (validated path/argv/envp into the
initial user stack), `Scheduler.adopt_authenticated_executable_pid_with_launch_v1`
(revalidates before touching the one-shot token; records the owned command via
`scheduler_execution_observe_adoption_with_launch_v1` before publication),
`fs_exec_adopt_authenticated_with_launch_v1`, and
`x86_64_fs_exec_spawn_authenticated_with_launch_v1` (v2 handoff, exact reap,
evidence only through `scheduler_execution_compare_and_deliver_reaped_v2`).

Evidence: `test/01_unit/os/kernel/loader/x86_64_fs_exec_launch_owner_spec.spl`
(red "function not found" -> green 2/2) and
`test/01_unit/os/kernel/scheduler/authenticated_launch_arguments_threading_spec.spl`
(red "method not found" -> green).

Still open: (1) guest execution proving the child receives argv/envp;
(2) a signed-admission unit proof that the prepared image carries argv/envp —
blocked because `executable_admission_pipeline._loader_read_binding_exact`
still rereads through text `pread` (NUL bytes overrun `text_to_bytes_pure`),
and with a byte-exact reread patched in, pure-Ed25519 admission exceeded the
900 s test budget; (3) the arm64 owner still adopts path-only.

## 2026-09-28 update — admission reread fixed; ">900 s" not reproduced

Profiled with the smallest input (the 132-byte fixture ELF) under
`bin/simple test`, binary `bin/release/aarch64-unknown-linux-gnu/simple`
(51838272 bytes, 2026-09-26 16:44, sha256 `44a07ae51c5dd308...`, Rust seed).
Per-phase wall times: keypair 0.35-1.0 s, sign 0.7-2.1 s, direct verify
~1.5-1.9 s, admission reread 1 ms, sha 10 ms. Neither the reread nor
pure-Ed25519 costs hundreds of seconds; the >900 s figure was on an unlanded
local patch and is not reproduced on main.

The real defect was correctness: `_loader_read_binding_exact` reread the image
through text `pread` + `text_to_bytes_pure` (per-char copy), which crashes on
the NUL-bearing ELF (`string index out of bounds: index is 132 but length is
132`). It now makes one bulk binary read through
`MountTable.read_execute_binding_exact_v1` (retained binding, revalidated).
The spec fixture also moved to NVFS + `positioned_write_bytes` (RamFS via the
MountTable has no text-write arm and drops its fd table) and to
`executable_loader_trust_roots_boot_initialize_v1` (the public initializer is
inspect-only).

Evidence: `authenticated_launch_arguments_threading_spec.spl` example
"rereads the admitted image byte-exactly before signature verification":
red on main (the crash above, 1/2, 19 s) -> green 2/2 in 30 s.

Item (2) above is now narrowed: the full argv/envp prepared-image proof is
blocked on an aarch64 host because the interpreter picks `@cfg` by
`TargetArch::host()` (`interpreter_eval.rs:523/721`,
`interpreter_module/module_loader.rs:1000`), so ELF layout after signature
verification reaches freestanding `@cfg(arm64)` externs
(`byte_utils.byte_at` -> `rt_arm_array_get_byte_u32`, `elf_loader.spl`
`rt_arm_elf64_*`) that the hosted interpreter does not register
(`unknown extern function: rt_arm_array_get_byte_u32`).
