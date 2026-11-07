# Owned controller journal startup and cleanup

Status: **NOT_RUN**. Authored manual; no generated/native/runtime PASS evidence.
Requirements: ORCH-02 complete replay and cancellation; HOST-02 retained ownership.
Spec: `test/03_system/app/orchestrator/feature/controller_workload_store_owned_v2_spec.spl`.

Setup: acquire the actual owned SDK journal under a secure temporary root using
valid controller authority and nonce. Use actual AgentSession/catalog files and
production submit/pin/preflight/workload/cancel APIs. The canonical owned journal
and file-lock dependency is combined separately; no dependency source is copied,
no live owner or WAL is mocked. Every normal close requires no cleanup, closed,
empty error and Released state. Unexpected cleanup is explicitly attempted and
fails the scenario rather than being reported as success.

| Exact step | Procedure / checks |
|---|---|
| replays desired policy preflight child and cancellation through the actual owned journal | Submit and pin actual desired policy, associate preflight, create child, cancel parent. Close/reopen through owned path; exact source, parent marker, child cancellation and retained association persist and guard refuses execution. |
| retains actual cleanup ownership after lease mismatch until exact lease restoration | Tamper own real parent lease. Close returns Retained with actual cleanup owner and stale-lease error. Restore exact bytes, clean the retained owner, then reopen successfully. |
| rejects foreign replay domains and releases the actual owned journal on projection failure | Admit a foreign domain through actual journal SDK. Store projection rejects it; independent raw SDK can reacquire/release the same journal, proving ordinary failure did not lose the lock. |
| preserves stale typed close failure instead of treating absent cleanup as success | Close real owner successfully, then close its stale copy. SDK state remains Stale, closed=false and nonempty error despite no cleanup payload. |
| retains both actual journal cleanups through the app reply without promoting later release | Acquire two independent actual journals, invalidate both leases, and pass both retained cleanup owners through the application's finalizer. Both remain retained and the wire reply reports uncertainty. Restore exact leases and finalize again: both release, but the previous failed command remains nonzero and its reply is not promoted. |
| refuses an ownerless error state without inventing a cleanup retry | Pure finalizer invariant: a zero-exit reply carrying ConsumedError, Unknown or Stale but no owner becomes nonzero while retaining its state and no fabricated owner. This is not native close fault injection. |

The existing replay body is unchanged and shared by legacy and owned open:
workload revisions, assignment records, desired input/cancellation, pinned policy,
preflight association and pending metadata completion retain their prior rules.
No foreign records are silently skipped. Failed projection closes through the
owned SDK; Some cleanup is returned, never discarded. No owner remaining permits
Rejected, with cleanup error preserved. The close wrapper returns the SDK typed
turn unchanged: nil+closed=true+error (ConsumedError) is still failure, never a
successful boolean. Retained/Unknown require keeping cleanup; Stale is not fresh
authority. Actual consumed-close-error/unknown native fault injection is NOT_RUN
and not fabricated by these scenarios. Legacy Result open/close remain only for
compatibility; new owned code does not call them. Journal process-crash replay
is not power-loss durability, runtime stop, capacity release or execution approval.
The metadata CLI and all four dispatch/preflight functions use the owned open
and close path. The dispatch turn carries both controller and nested host
cleanup independently, including errors while archiving a host response. A
failed host turn blocks subsequent host calls. The application's reply retains
both owners and their typed release states; neither is serialized as authority.
The compiled entrypoint makes at most one further exact cleanup attempt for
each retained owner before output. Unresolved or consumed-error results remain
nonzero. Process exit intent is not release evidence. Persistent callers must
retain unresolved owners beyond their wire response and prohibit new mutation.

The four in-process dispatch return types now carry ownership rather than a
text-only Result; their sole application caller is migrated. Public successful
SDN response formats are unchanged. Workload-store legacy Result APIs remain
compatibility surfaces and are not called by production controller paths.
Builds/tests were prohibited for this task.
