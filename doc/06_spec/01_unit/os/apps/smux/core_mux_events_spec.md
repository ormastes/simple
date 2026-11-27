# Bounded CoreMux event journal

Source: `test/01_unit/os/apps/smux/core_mux_events_spec.spl`.
Requirements: REQ-CMUX-008/010. **NOT_RUN: ten authored cases, zero executed.**
Manual prepared from source; canonical docgen and actual SSpec evidence pending.

Each case calls the production journal. `event_setup` constructs one bounded
explicit lease journal; `event_check_batch` compares literal expected cursors,
owner identity and reconciliation. Values model observations only; no case claims
a native child event, authenticated lease, running provider or consumed output.

| Case | Required observation |
|---|---|
| Construction and binding | Empty batch; invalid count/byte limits refuse; different lease, owner or generation cannot advance, append or read. |
| Cursors and causality | Assigned cursors 1,2; arbitrary causal IDs 99,1 and supplied revisions preserved; original value unchanged. |
| Count eviction | Three events in two slots retain cursors 2,3; reading before loss floor requires reconciliation, reading at it does not. Future cursor refuses. |
| Byte budget | Canonical batch overhead is charged; one-event budget evicts older data. One byte below the next-event bound refuses; exact conservative budget succeeds. |
| Oversized valid event | A valid event larger than retention consumes its cursor, clears retained history and advances loss floor. A subsequent smaller event resumes retention without hiding the gap. |
| Malformed input | Zero causal ID, foreign reference and empty object ID refuse without cursor or retained-state change. |
| Serial exhaustion | Pure near-u64-limit state permits one remaining advance, rejects two, and never wraps. Final event remains readable. |
| Pagination | Count-limited pages return contiguous cursors; repeated read is unchanged. Insufficient reply overhead refuses rather than skipping data. |
| Internal invariants | Empty/missing retained tail, duplicate cursors and invalid count limits refuse through the actual production paths. These are structural controls, not allocator-failure injection. |
| Escaped Unicode | Notification receipt includes Unicode/quote/backslash data; actual canonical serializer output stays within the codec's conservative batch charge. |

Byte tests distinguish a conservative encoded-size bound from the actual
serialized byte length. The helper reuses the existing codec sizing and SDN
serializer rather than implementing a second parser/encoder. No fake byte-charge
argument is accepted. These tests do not certify whole transport-envelope size.

Root owns serialized Phase 2 execution with the actual supported producer
profile, positive/negative framework preflight and retained case counts. These
authored cases are not compile, native-control or SSpec PASS evidence. Full
owner mutation/event integration, lease authentication/revocation, native event
observation, socket behavior, complete provider admission and N2 remain pending.

Cycle 3 adds checked singleton/copy/append/slice/reply cardinality and final
canonical validation. Construction failure returns Unavailable without advancing
a returned cursor past missing records. The structural controls are not actual
allocator exhaustion, which remains unexecuted.
