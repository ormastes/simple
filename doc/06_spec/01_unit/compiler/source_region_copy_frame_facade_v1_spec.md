# SOURCE copy-frame common facade controls

Execution: **UNRUN**. This is a hand-authored manual for the corresponding
executable spec, not generated or fabricated runtime evidence. Native-only
sanitizer evidence is retained separately and is not repeated here.

Each scenario creates an actual account and request, then enters a real native
module scope. Teardown uses copy cleanup, ReadEnd, revoke, release and module
end. Assertions exercise actual outcomes; no fabricated provider success exists.

| Requirement | Scenario and observable result |
|---|---|
| COPY-COMMON-1 | Prepare charges the request's actual account before the lease; allocation returns a positive raw pointer; its copied scalar reads 37; another allocation refuses. Cleanup retains the lease until successful ReadEnd resets common state. |
| COPY-COMMON-2 | A wrong epoch refuses ReadBegin; prepared-only cancellation resets the frame without inventing a lease. |
| COPY-COMMON-3 | Corrupting only common lease correlation makes native cleanup refuse; ReadEnd preserves its credit. Restoring the genuine lease allows one explicit cleanup retry with increased same-account work, while preserving the original cleanup error. |
| COPY-COMMON-4 | A real unrelated raw allocation invalidates the prepared revision. Copy allocation refuses and cannot retry; the retained frame remains cleanup-able. |
| COPY-COMMON-5 | Exhausting account work rejects preparation before native frame ownership, while existing prepaid request teardown remains available. |

Run only in a separately authorized resource-guarded compiled native test slot.
Interpreter/provider-absence execution cannot qualify native ownership. The
fixture does not qualify compiler confinement, stores/publication CFG,
hosted/pure parity, 32-bit targets, wall time or RSS guarantees.
