# Installed guest compiler version operation

Scope: the first loader-owned execution slice for REQ-017/REQ-018 and UP-AC-006.
The selected platform-unification requirements and architecture remain the
governing design. This addition does not complete either requirement.

`simple_guest_version_execute_v1` takes the exclusively owned Scheduler and
`mut table: MountTable`. The mutable parameter aliases the caller's table, so
execute-open, admission, submission, and cleanup mutations survive all returns.
A plain table parameter would copy the struct and lose those owner updates.
Mutation propagation still needs native operation testing. Scheduler updates
are returned in both success and error results.
It derives the current task and concrete capabilities through the
scheduler snapshot lease, consumes that lease, obtains the active target and
sealed installed compiler record, and uses existing online authenticated
filesystem admission. The app-launcher recipe confines execution to `/sys/apps/`;
this operation further fixes `/sys/apps/simple_compiler.smf` and `['--version']`.
It exposes no path, argument, caller-ID, capability, exit-status or output input.

The submission service owns executable authority cleanup. The operation consumes
every returned scheduler evidence token, including failed submissions, before
returning. Missing evidence, cleanup uncertainty, failed execution, wrong parent,
wrong compiler digest/path/target, invalid generations, empty stdout, truncation,
or either output stream above 4096 bytes prevents a success receipt. Scheduler
capture remains bounded by its existing 65536-byte per-stream ceiling; the
receipt's stricter limit does not change that scheduler-wide policy.

The receipt retains the observed child/parent/generation, executable digest and
filesystem generations, target, captured bytes and their SHA-256 digests. The
private receipt constructor receives only consumed scheduler observations.
The package-visible pure validation predicate creates no execution authority.
Negative specs exercise that predicate using explicitly synthetic observations.

Qualification remains RED: no guest boot caller has been wired here, no live
execution was observed, and candidate/derived-image/boot-session/compiler-release
version binding plus guest compile/run/native/reboot persistence evidence remain
required. A nonempty successful version command records output; it does not
assert that the output matches a particular release version.

Verification limitation: the local release-path binary identifies itself as a
Rust bootstrap seed and fails in unrelated process_ops.spl parsing. It was not
used again. No source-matched admitted pure-Simple runner is available locally;
spec execution and compilation remain pending. Static diff and environment
guards are the only local checks claimed. Parent review is required before
commit/push; CI cannot substitute for the missing live cold-boot evidence.

Ownership: implementation lane `simpleos_version_owner_impl`; parent is merge
owner and final reviewer. Additional sidecar implementation lanes: N/A.
