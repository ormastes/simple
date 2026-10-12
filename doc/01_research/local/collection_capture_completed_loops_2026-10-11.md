# Completed adaptive set loop capture

REQ-PSC-003 requires applicable measured collection work. The existing typed
loop normalizer accepts only a narrow append loop and has no stable capture
site transport for arbitrary break/continue loops. General compiler loop
instrumentation remains open. This slice adds an explicit observed set-loop
API, using the caller's existing collection identity and target.

`adaptive_set_for_each_observed` validates a complete sorted unique snapshot,
copies the source identities before callbacks, records the snapshot cardinality,
and counts each actual callback entry. Continue and the entry returning Break
count once. Callback Err has no completion event; effects already performed
remain visible. Successful empty input records zero trips. Capture failure is
reported at profile finish and leaves the completed logical result intact.

The existing process capture owner accepts the new event only for an already
observed collection site. It rejects negative counts, overflow, invalid sites,
and an extra metric exceeding the 100000-row cap. It sums completed trip counts
under the capture lock. Untouched sites omit the metric; completed empty loops
emit `loop_trip_count=0`. The interpreter adapter and native ABI use this same
owner; the loader already admits `loop_trip_count`.

The opt-in API keeps existing set traversal unchanged. Its snapshot retains
the existing sorting/materialization costs, adds a validation pass, and emits
one completion event per invocation. Disabled capture returns before allocation
or locking. No file I/O or profile scan occurs in the event path. Latency/RSS
comparisons and Simple wrapper execution remain unverified.

The changed native C selfcheck compiled with clang and ran once, both exit 0.
It checks sum 5, target isolation, measured zero versus absent, unknown site,
negative counts, signed overflow, and full record-budget rejection. The Simple
unit spec has real callback and capture assertions but remains UNRUN pending a
source-matched runner. This evidence does not qualify Phase 3 or full item7.
