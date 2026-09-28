# x86_64 typed handoff result prerequisite

Base: `22d74189e38`, isolated native ABI prerequisite, 2026-09-28.

## Implemented

`baremetal_stubs.c` now exposes
`rt_x86_exec_token_take_result_v2(task, generation, cr3, int64_t *out_rc)`.
Return 1 consumes the exact matching completion and writes all 64 status bits;
return 0 leaves the output and any pending completion unchanged. The output
must be a valid kernel-owned writable pointer. Null is rejected. The existing
v1 API remains available with its original -4096 sentinel ambiguity.

Installation rejects both an active token and an undelivered completion. The
real exit producer uses the same completion transition compiled by the native
test. Both APIs consume the same result slot exactly once.

## Evidence

`sh test/01_unit/os/kernel/arch/x86_64_exec_token_result_v2_test.shs` passed
once with C11, `-Wall -Wextra -Werror`. The test compiles production state and
transition functions extracted from the runtime, excluding privileged CR3
reads and unrelated freestanding dependencies. It covers missing result,
invalid installation, active/pending overwrite refusal, wrong task/generation/
CR3, null output, replay, cancellation, v1 compatibility, and guest statuses
0, -16, -22, -4096, INT64_MIN, and INT64_MAX. `git diff --check` passed.

This is native serialized lifecycle evidence. It does not test user-pointer
validation, CR3 authentication, assembly entry/resume, SMP concurrency, or a
complete runtime build. No source-matched Simple runtime was used.

## Remaining owner contract

The global token/result slot remains serialized boot-only state; this patch
adds no lock or per-CPU ownership. A typed Simple bridge must preserve this
restriction until the owner enforces serialization across install, entry,
completion, take, and cancellation. It must pass a kernel-owned output slot
and distinguish `Exited(status)` from validation/install/missing-result errors.

`x86_64_fs_exec_spawn.spl` currently converts every scalar handoff return into
a scheduler exit and reap. Only an authenticated `Exited` result may produce
execution evidence; handoff failures need separate cleanup. The launch-aware
image/adoption route still must bind canonical path and real caller authority,
use the same validated argv/envp for stack construction and pre-publication
command observation, and retain exact-child one-shot reap/delivery semantics.
The initial-RSP selection fix is separately owned by PR #1888.

## Typed Simple bridge follow-up

`arch/user_handoff_result_v2.spl` separates `Exited(i64)` from typed failures.
The x86 owner validates first, acquires a native fixed eight-byte output
slot, consumes native v2, and reads the initialized slot with the existing
`rt_volatile_read_u64` ABI. Release checks the exact pointer and busy state;
the bridge checks release success on every returning path after acquisition.
Overlap is rejected and an interrupted owner leaves the slot busy, failing
future admission closed. These operations retain the serialized boot-only
precondition; they do not provide SMP locking or transferable lease tokens.
`rt_ptr_read_i64` is deliberately excluded because its x86 implementation
encodes tagged ints. No heap allocation occurs in the bridge.

The architecture-neutral facade exports the typed x86 route; other targets
explicitly return UnsupportedArchitecture. Scalar syscall compatibility still
exists, but authenticated x86 execution now consumes the typed result.

`x86_64_fs_exec_spawn_authenticated_result_v2` returns the typed handoff and
the mutated Scheduler. Failed handoffs retain the task and mapping, fence it
as PreparingExit, and remove its ready entries without recording exit or
calling wait. This is quarantine, not reclamation or guest completion. Only
Exited reaches exit/wait; collection checks the exact PID and parent. The
legacy scalar facade discards returned ownership and is not a recovery API.
Callers needing failure recovery must use the result-returning route. Command
evidence and argv/envp adoption remain outside this increment.

Follow-up evidence:

- The first follow-up used a heap output slot. Its test harness initially
  missed NIL_VALUE, and compilation passed after repair. Review then rejected
  this design because target free is a no-op. That design was removed.
- The third/final verification cycle compiled the production fixed-slot owner
  and raw-read function and passed full-i64 round trips, address reuse, overlap
  refusal, null/wrong-pointer release, and repeated-release rejection. The test
  no longer uses host free to hide target allocation behavior.
- Updated typed source-wiring guard and failed-handoff-exit sabotage detection
  passed in that final cycle. This checks source structure, not Simple execution.
- Added typed-result and scheduler-quarantine Simple specs. They were not run:
  the sparse worktree has no `bin/simple`, and no admitted source-matched
  self-hosted runtime is available. No seed fallback was used.
- Direct environment guards cover the working and staged changes. The sparse
  checkout does not provide full-tree runtime admission evidence.
- Whitespace check passed during the first follow-up verification cycle.

Global native token serialization, quarantine reclamation, full native kernel
build/link, and live guest execution remain unverified or unimplemented as
specified above. These prerequisites do not establish a release-ready launch.
