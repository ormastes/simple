# Owner-bearing operation-journal startup

Status: source implementation and authored regressions; all runtime cases
**NOT_RUN**. No compiler, native test, or bootstrap campaign was attempted.

The existing Result startup acquired `parent.lock` before lease publication and
WAL replay. Its error paths ignored `file_unlock` failure. The legacy native
unlock attempts close even when unlock fails; a false result can therefore
refer to an already-consumed descriptor. Retrying that integer could affect a
different descriptor reused by the process.

The additive owned entry uses the same lock path, OS lock namespace, lease
format and segmented database WAL. `DistributedOperationJournalOpenV2` returns
Ready, Rejected, or CleanupRequired. A cleanup value contains root, authority,
lease digest/publication state and the actual native generation owner. It is
not an empty journal and has no WAL mutation port. The same cleanup operation
handles opened-journal close. Every caller must retain the typed cleanup turn.

The canonical native table has 256 bounded slots, nonwrapping monotonically
allocated tokens, PID correlation and serialized phase changes. Tokens never
encode descriptors. Polling acquisition occurs outside the table gate; its
slot remains exclusively acquiring. Release rejects copied stale tokens before
any native action. A process-origin check precedes the atomic gate, so forked children refuse
all owner calls even if the parent gate was held at fork. They must exec before
using the registry; copied tokens cannot unlock the parent's shared open
description. The regression holds the gate across fork and bounds refusal.

| Release state | Owner returned | Meaning |
| --- | --- | --- |
| Released | none | Native unlock and close succeeded |
| Retained | exact generation | Unlock failed without close, or Windows close failed |
| Unknown | quarantined generation | Non-Linux POSIX close failed; no descriptor retry |
| ConsumedError | none | Linux close consumed the fd but returned an error |
| Stale | none | No matching live generation; never successful own close |

Linux invalidates the canonical slot before close, including EINTR. Windows
keeps the exact HANDLE when CloseHandle fails. Other hosted POSIX close errors
are conservatively quarantined because descriptor consumption is not inferred.
Unknown is not retryable native cleanup or positive absence; any quarantined
slot refuses all new owned acquisition in that process. Only Held authorizes journal mutation. Release never fabricates an
absence receipt or a fresh owner. Acquisition cleanup failures also expose their
real retained generation. The Rust provider delegates to the same C owner,
including its interpreter bindings; it does not reuse legacy reentrant locks.

Cleanup verifies native ownership before reading/deleting a published lease,
checks the exact lease digest and retains the owner if removal fails. It records
lease removal before a fallible unlock so the returned retry value does not
delete a subsequent owner's lease. Stale copied cleanup never touches a lease.
The configured journal parent remains trusted against concurrent hostile path
replacement, as in the existing WAL owner; this change adds no path authority.

Legacy Result open remains for existing callers while host-capacity and
controller-workload startup migrate to the owned result. New services are not
admitted through that old entry. Legacy Result close rejects a new owned journal
before effects because Result cannot carry a partial cleanup turn. No legacy
wire or WAL migration is required. Root owns migration closure and service
admission; the additive owner change alone does not claim that closure.

Regressions use actual native locks, real handles, temporary files and the real
WAL API. Compile-time test wrappers inject a selected unlock or close failure;
there is no production fault flag. Linux cases cover contention, failed unlock,
consumed EINTR, generation reuse, forked stale copies and process death.
Windows cases cover failed-close retention, acquisition cleanup retention and
UTF-8 Unicode path correlation. A macOS/FreeBSD-only case covers actual
descriptor close uncertainty, no retry, and global owned-acquisition refusal.
Simple integration cases cover ownership/reopen, corrupt CURRENT replay and
exact lease mismatch. These authored cases do not prove runtime behavior until
run under an independently authorized native/compiler slot.

Static review evidence: the working direct-environment guard passed. The
initial `git diff --check` passed; the final staged check is recorded with the
immutable handoff. The RT pointer map reported one existing mismatch for
`linux_process_owner.spl:rt_linux_group_collected_stream_v2`; the host map
reported 27 existing non-Linux `rt_linux_group_*` provider gaps. Neither script
reported an owned-lock symbol finding. These failures are not a global PASS,
and their compile/link coverage remains UNTESTED. No baselines were changed.
Windows acquisition strictly converts the bounded UTF-8 path to UTF-16 and
opens with CreateFileW, matching the WAL path rather than an ANSI codepage.
