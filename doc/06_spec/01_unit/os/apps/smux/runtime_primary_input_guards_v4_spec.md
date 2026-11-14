# smux primary input V4 pure guards

Source: `test/01_unit/os/apps/smux/runtime_primary_input_guards_v4_spec.spl`.
Status: **NOT_RUN**. Manually authored companion, not executed acceptance evidence.

Seven scenarios directly exercise production helpers:

1. Same attempt and full V4 request digest returns the cached result; changed
   payload and old sequence are refused.
2. An Unknown prior attempt blocks a later sequence, revision, or session.
   Lease rotation supplies no evidence that delivery did not occur.
3. An exact Recorded native last tuple reconciles Unknown metadata for zero,
   partial, or full requested prefixes, retaining native status information.
4. Every mismatched tuple field, absent last history, Unknown/Rejected native
   disposition, and out-of-range accepted prefix preserves the saved Unknown
   record. Already recorded results retain their original metadata.
5. Lease revision and millisecond deadline limits enforce the native ceiling;
   valid deadlines convert exactly to nanoseconds.
6. Installed-state recognition requires controlled/active state and matching
   full target digest, nonce, revision, and native deadline. Changed target
   scope, runtime, workload, binding, service, pane ancestry/incarnations,
   attachment, or execution domain cannot match the saved installed state.
7. A genuine pure primary plan fixture correlates scope, runtime, workload,
   binding, and primary execution fields; stale plan digest or drift is refused.

Native-state and lease values in this file are metadata inputs only. These
checks do not install a live gate, mint authority, write input, prove delivery,
retry a native operation, rotate a real holder, or prove cleanup. Native slot
history has no payload digest: reconciliation is tested only against an
already saved full-request digest. Server integration, canonical live session
ownership, native locking, actual partial writes, and native receipt durability
remain outside this source-only specification.
