# Actual Linux protected Host setup/publication/reader fixture

Source: `test/02_integration/lib/io/linux_host_auth_protected_native_v1_spec.spl`.
Status: AUTHORED_NOT_RUN. Missing prerequisites fail instead of skip or fabricated success. No fixture was provisioned and no native/compiler/service campaign ran.

Use a disposable current-user0700 directory under existing trusted non-writable ancestors. Prepare its `deployment` child0700; leave `credentials` and `deployment/journal` absent or fresh. Set SIMPLE_LINUX_HOST_AUTH_FIXTURE to its canonical absolute spelling. The test creates real private setup with actual OS entropy, a genuine protected journal/flock, a real loopback listener, immutable ready publication through the same journal, and the actual protected reader. It preserves all failed competing-open cleanup outputs and all publisher/reader/journal cleanup outputs. Published files intentionally remain for inspection; do not reuse the target for another fresh publication.

The success flow checks competing writer refusal without changing the live lease, real same-WAL transition/replay of one DATA-only storage fixture row, no-replace conflict preserving exact original artifact bytes, real listener endpoint/incarnation and setup/ready/lease pins, and old-reader refusal when a genuine new writer changes the lease. The row is not a signed grant, resource charge, fake reservation, helper permit or execution proof. Closing the journal alone never claims service death or releases capacity.

For SIMPLE_LINUX_HOST_AUTH_INPUT_FIXTURE prepare a separate private root0700 with `input.sdn` a real current-user0600 regular single-link UTF8 file, `unsafe.sdn` an operator-planted symlink to a benign fixture file, and no `definitely-absent.sdn`. The readonly specimen checks first and repeated cached reads of the same actual retained input (including each read's own full ancestry postcheck), currentness, immediate alias invalidation when cleanup begins, actual ENOENT versus symlink refusal, sticky currentness refusal and owner-bearing cleanup. It never prints private bytes. Parent cleanup retains latest returned owners and each pending competitor; owner absence proves only consumed custody, not absence of diagnostic errors or target deletion.

Additional mandatory native fault matrix (MANUAL_NOT_RUN; no fault producer is invented):

| Case | Actual fault and required observation |
|---|---|
| Principal/mode/type | Wrong euid ownership, final0755, file0644, hardlink or nonregular target refuses; no legacy fallback or secret write |
| Permissions before bytes | Observe exclusive600 stage and positive metadata checks before the first private write; restrictive umask cannot expose bytes |
| Cached-read postcheck | Retain input once, repeat the real cached read, and use a genuine concurrent fault controller to rename/rebind an ancestor after the initial current check but before the read finishes. No bytes may escape; the stable cell must quarantine and retain exact cleanup. No such timed injector exists in this lane: NOT_COVERED; the positive repeated-read specimen is not a deterministic prior-failure reproduction |
| Ancestor/file substitution | Rename/rebind an original ancestor or retained immutable file; current/MAC refuse, same slot retains exact cleanup |
| Stage substitution | Replace stage name after acquisition; cleanup must not unlink substituted object; original held resources remain pending |
| Selector race | Replace parent.lease during before/after bracket; ready admission/current refuses; old selected inode is never reused as selector authority |
| WAL integrity | Corrupt immutable object or CURRENT; replay refuses and cleanup retains the original protected writer; rows stay charged absent authoritative settlement |
| Partial acquisition | Fail allocation/open/stat after actual FD acquisition; latest canonical cell still owns each FD |
| Publication ambiguity | Fail write/fsync/link/rename/directory-fsync/readback at each boundary; quarantine, no retry/compensation or fabricated publication receipt |
| Consumed close | Inject real close error/reused-fd pressure; canonical slot is consumed before syscall, raw FD is never retried; terminal error remains nonsecret |
| Metadata gate failure | Fail oracle lock/unlock after IO; actual native consumption remains shared and retirement does not reconstruct a resource |
| Fork/thread/PID namespace | Use a real inherited owner in a child/non-main thread/nested PID1 namespace; genuine existing origin guard refuses before registry/mutex access; no reset/fallback |
| Authentication | With real wire R3 connection/exchange owners check fresh challenge success, replay refusal, mutated tag and V6/V7 purpose separation; no fake reader/handles |
| Diagnostic PID | A saved PID value alone never enables lifecycle, kill, capacity settlement or external pidfd adoption |

Real fork/thread/failure-injection producers and complete installed Host/server fixture qualification are unavailable in this authored lane. They are NOT_COVERED, not passing tests. Existing pure codecs/earlier wire cases are dependencies, not new execution evidence. Independent source acceptance, full Host startup composition, native linkage, remote/live exchange and endpoint/workload readiness remain unqualified.

Corrective source history: R1 independent source review found LINUX-AUTH-R1-P1-01 (missing explicit WalEntryType import in extracted replay) and P1-02 (cached read missing full post-IO ancestry validation). R2 corrects both in one batch. Existing actual nonempty WAL/reopen specimen exercises replay Insert decoding when executed; repeated actual input reads exercise the retained cache branch. All cases remain AUTHORED_NOT_RUN. Source inspection establishes the added import/postcheck; no compile or concurrent fault reproduction is claimed. Broker root-match/16MiB extensions are excluded from this corrective candidate.
