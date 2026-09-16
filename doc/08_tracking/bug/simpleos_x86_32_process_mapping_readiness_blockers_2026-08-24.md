# SimpleOS x86-32 process mapping readiness blockers — 2026-08-24

The authenticated ELF32/i386 metadata path is present, but filesystem-launched
x86-32 execution must remain blocked before loader authority consumption.

- `stack_builder.build_initial_stack_checked` accepts only `abi_word_size == 8`
  and emits eight-byte argc, pointer, and auxv slots. The x86-32 System V ABI
  requires a bounded four-byte serializer with 16-byte entry alignment.
- `arch/x86_32/paging.spl` creates two-level process page directories but its
  map/unmap/translate calls use only `g_vmm.pd_phys`. The scheduler adapter
  instead calls the x86-64 PML4 explicit-root implementation for `@cfg(x86)`.
- No x86-32 owner currently rolls back partially mapped leaf frames and private
  page tables or destroys a process page-directory tree on every failure.
  The bounded `arch/x86_32/user_page_root_owner_v1.spl` prerequisite now issues
  explicit roots, serializes map/unmap/destroy, rejects duplicate physical-leaf
  provenance across roots, retains private tables, and reports quarantined
  ownership explicitly on indeterminate publication. It intentionally does not
  map authenticated ELF ranges or own rollback of caller-owned data frames, so
  the full process-image mapper remains incomplete.
  The loader-owned `x86_32_authenticated_mapping_owner_v1.spl` now closes the
  mapping-side prerequisite: it revalidates the digest and exact PT_LOAD layout,
  owns exact allocated leaves, performs copy/BSS-zero readback, creates a
  four-byte initial stack, and retains retryable/quarantined teardown state.
  It reports the non-PAE absence of hardware NX/W^X and deliberately publishes
  no scheduler or execution authority.
- Three static design/review cycles rejected an attempted explicit-root owner.
  The remaining safe design requirements are: an authoritative create-issued
  root and unique-leaf registry; duplicate physical-frame aliases must be
  rejected; map and destroy must serialize; every fallible lock/unlock boundary
  must end in a retryable `Active`, `Released`, or `Quarantined` state; a
  teardown that already freed the tree must never report a retryable failure;
  and every quarantine path must return an owner/lease rather than orphaning
  the root. The unsafe draft was reverted.
  A further three-cycle attempt on 2026-08-24 was also reverted. Its in-flight
  nonce protocol safely serialized callbacks and rejected copied/re-entrant
  authorities, but the available blocking-only raw mutex cannot close this
  race: a waiter may pass an atomic fail-stop precheck immediately before a
  prior unlock fails while retaining the mutex, then block forever. The draft
  also initially returned a provisionally registered leaf on that failed
  unlock, which would permit aliasing/double-free. Resume only after a proven
  nonblocking try-lock/fail-stop primitive or an owner protocol that cannot
  strand waiters is available; committed provisional leaves must never be
  returned to callers.
  A subsequent static review established that merely exposing the existing
  hosted `spl_mutex_try_lock` through the scalar Pure Simple facade is not that
  primitive: the SimpleOS-linked `src/os/kernel/net/thread_shim.spl` currently
  implements mutex try-lock and unlock as unconditional success, so copied
  owners can concurrently enter on the actual target. A callback wrapper also
  cannot make page-table registration or mapping provisional merely by
  discarding its return value after unlock failure. The target backend needs
  shared atomic lock state, and the page-root transaction needs an authoritative
  rollback/quarantine owner (including the case where unlock released but
  reported failure) before a receipt may escape. The rejected wrapper and its
  hosted-only specs were reverted; no target exclusion claim is retained.
- Classic two-level non-PAE i386 has no NX bit. The mapping receipt now reports
  `hardware_execute_disable=false` and `hardware_wx_enforced=false`; selecting
  PAE/NX remains necessary for any future hardware W^X claim.
- A consume-once scheduler adoption must transfer the future mapping owner into
  a task, install its CR3 for CPL3 entry, and invoke terminal destruction.
  The canonical TCB now appends an opaque generation-bound x86-32 mapping
  locator. Every constructor and fork path initializes it absent, and legacy
  exec rejects a present locator. There is intentionally no present-locator
  constructor: the remaining blocker is an owner-consumed mapper-to-scheduler
  transfer bound to the exact TCB lifecycle, followed by terminal reap. The
  locator exposes neither the page-directory address nor mapper teardown
  authority.
  The package-private transfer prerequisite now has a bounded scheduler-owned
  reservation capsule and typed commit/reject/indeterminate result. It retains
  and compares the complete admission handle before mapper lookup, validates
  exact mapping receipt/entry/stack evidence, and publishes an opaque locator
  only after both owners commit. Exact slot/generation/nonce cancellation burns
  abandoned task identities; an indeterminate unlock poisons the entire owner
  without touching slot memory afterward. Static review is still required.
  Production remains blocked on a scheduler-owned transaction that consumes
  the committed locator and identity into one unpublished TCB, publishes it,
  and owns exact mapper destruction on terminal reap. No CR3 activation or task
  table mutation is claimed by this prerequisite.

Until those owners join the scheduler transaction,
`executable_target_dispatch_v1` must retain
`process_image_builder_ready = false` for canonical architecture `x86`.
