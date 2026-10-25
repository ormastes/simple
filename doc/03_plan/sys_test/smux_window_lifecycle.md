# smux window lifecycle acceptance

Requirements: selected A/N2 REQ-CMUX-002/004/005/008/010 and
NFR-CMUX-005/006/008/009. Nine authored scenarios, zero executed: NOT_RUN.

Executable: `test/03_system/tools/smux_window_lifecycle_spec.spl`.
Manual: `doc/06_spec/03_system/tools/smux_window_lifecycle_spec.md`.
Design: `doc/05_design/smux_window_lifecycle_2026-10-25.md`.

1. Use the verified Phase 3 Windows producer and real native provider roots;
   retain source/compiler/provider identities and actual assertion counts.
2. Run this native SSpec once with an external 120s process-tree watchdog per
   native case. Retain failed/pending cleanup instead of discarding its owner.
3. Generate/review the manual and run the SSpec maintenance scanner when the
   admitted runner supports them; require zero placeholders and current mirror.
4. Extend/run the existing real external-owner/two-attach-client fixture pattern
   in a separate owned fixture: both terminals select W1, kill W1 through a
   lease-scoped command, independently observe both clients remain alive and
   render W2's child-computed marker. Send distinct fresh input to each client
   and verify only W2's actual child receives it; failed W1 input must never be
   retried there. Delete final W2 and require both client processes exit 0 with
   terminal modes restored. Preserve process/console and cleanup receipts.
   This external-console scenario is still an execution/fixture gap, not one
   of the nine authored SSpec passes.
5. Exercise real provider deferred/failing close and retain original handle
   authority. Verify closing-window input/spawn/rollback refusal, retry after
   native completion, and the transition from nonfinal to final pending close.
   No injected fake close or synthetic record may satisfy native evidence.

Native failure-path and client recovery evidence remain NOT_RUN. Existing
unrelated persistence suites and their running agents are unchanged. Parent
owns integration/merge; `astra_windows_final_review` independently reviews the
source and manual. Do not rerun unchanged passing criteria; six-cycle total
repair cap applies to this feature.
