# Bootstrap SCV prime must recognize the current publication

The bootstrap prime helper accepted only the six-line v1 cursor at
`build/scv/compile-events/CURRENT`. The compiler now publishes a v3 cursor
and inventory digest together at `build/scv/source-inventory/CURRENT`.
Consequently a valid current publication was treated as missing, cold
initialization was repeated, and the helper could still reject its result.
Running both backend lanes with forced cold initialization also caused
`compile-event-refresh-lock-unavailable` after the 300-second lock wait.

The helper now recognizes the combined publication and its inventory-digest
binding. A separate v3 cursor remains supported for legacy pointer layout;
v1/v2 require migration because warm refresh needs membership digests.
Malformed combined records cannot fall back to a separate cursor. The actual
compiler still performs warm admission and validates inventory content.

Recovery from missing filesystem-journal history requests a cold refresh
without deleting snapshots or cached artifacts. Callers should prime once
before launching parallel consumers and leave cold initialization unset for
those consumers.

Validation: all 21 focused helper checks passed, including combined-record
reuse, malformed binding, legacy migration, nonhex membership, retained
artifacts and warm admission refusal. The validator also accepted the actual
current combined publication in the Windows bootstrap source checkout.
These checks validate orchestration; Phase 3/4 and release admission remain
separate requirements.
