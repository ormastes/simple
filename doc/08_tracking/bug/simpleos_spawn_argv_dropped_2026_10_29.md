# SimpleOS SOSIX spawn dropped caller arguments

Status: implemented; host diagnostic unit evidence only. Guest execution and
self-hosted kernel qualification remain required before platform admission.

`src/os/sosix/process.spl` previously assigned caller arguments to
`_ignored_args` and invoked legacy syscall 13 with only path and priority.
Shared `ProcessLaunchSpecV1` planning preserves values, but its SimpleOS adapter
requires an injected service and does not itself provide kernel launch effects.
The old packed-vector kernel branch also resets the priority and installed x86
and RV64 direct bridges discard its vector fields.

## Implementation

The argument-bearing request uses the existing five-argument syscall surface:
path pointer/byte length in arg0/arg1, priority in arg2, owned u64 char** argv in
arg3, and `SYSCALL13_SPAWN_ARGV_ABI_V1` (`0x53504131`) in arg4. Legacy calls keep
their ABI. The scoped user owner reuses the bounded execve UTF-8 plan, writes raw
machine words, and frees the allocation after every syscall return. The kernel
copies the bounded NULL-terminated vector with the production VMM copy-in owner
before building the child image. Its priority remains arg2. Installed x86 and
RV64 bridges route the tag through this handler and adopt the returned scheduler.
The C syscall shim already forwards every argument into the same handler.

A supplied argv[0], UTF-8 bytes, order and empty later arguments are preserved.
An empty supplied vector retains the existing path-default launch. Invalid
inputs return errno through the existing async request completion table.

## Diagnostic evidence (macOS arm64)

Runtime: explicitly authorized P1 diagnostic bootstrap, SHA-256 prefix
`ddd5aa`; interpreter, no cache/database/session daemon, sequential/assert-ran.
This is not a self-hosted or guest qualification claim.

- New production source wiring: 4 failing examples before implementation,
  then 4 passing examples.
- New scoped raw owner: 2 failing examples before implementation, then 2
  passing examples. Its injected syscall probe reads actual raw char** slots
  and C bytes, verifies custom argv[0], UTF-8, empty arguments, priority,
  NULL termination, errno propagation and pre-submission rejection.
- Existing hot-path contract: 2/2 pass.
- Existing VMM copied UTF-8 text checks: 3/3 pass.
- Existing execve plan spec: 8/9 pass; the malformed UTF-8 fixture
  unexpectedly admits Ok (`unwrap_err` on Ok) under this diagnostic runtime.
- Existing process image spec: 1/6 pass. Failures concern old stack-top
  expectations (274877906944 versus 140737488351232), x86_32 initial-stack
  construction, and missing `_clear_synthetic_initramfs_for_test`. The explicit
  argv/envp image scenario passes. These source files are unchanged by this fix.

No P2 rebuild was performed. Physical trap dispatch, page-table-backed copy-in,
actual child argv observation, and cross-architecture execution remain separate
validation gates. The pre-existing imported `vmm_copyin_packed_string_vector`
has no definition in the current VMM copy-in sources; this change uses the
existing char** decoder and does not claim the old packed path is supported.

## Review corrections (2026-10-29)

Review traced the newly selected image-construction path into the scheduler and
found two existing defects that also affect argv spawn. The syscall handler
replaced the scheduler's registered physical child address space with a zero-root
placeholder. It now preserves the scheduler's registration, including the
mapping that owns the argv stack. The scheduler also reserved a second lifecycle
identity after creating the initial context. It now retains the single task and
generation pair reserved after mapping and entry validation.

Two step-based SSpec source-contract scenarios reproduce both defects before the
fix: the syscall body still registered a placeholder root, and the image owner
contained two identity reservations. With the same authorized P1 diagnostic
interpreter and flags above, all six scenarios execute: before correction,
4 pass and 2 fail; after correction, 6 pass and 0 fail. These assertions inspect
production ownership boundaries. They do not prove physical mappings, scheduler
execution, successful native kernel linking, or guest argv delivery. The legacy
packed-decoder gap above remains explicitly unverified.
