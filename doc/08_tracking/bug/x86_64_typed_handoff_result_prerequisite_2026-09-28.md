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
