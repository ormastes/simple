# Windows Engine control metadata consistency

Status: **AUTHORED SOURCE-ONLY NOT_RUN**. No tests or builds were executed.
The helpers check metadata and bounded progression. They do not issue authority,
authenticate a peer, validate a live grant, execute IO, or prove a native barrier.

Source: `src/lib/common/process/windows_engine_control_v2.spl`.
Spec: `test/01_unit/lib/process/windows_engine_control_v2_spec.spl`.

| Authored case | Intended assertion |
|---|---|
| First attempt | Exact live input binding accepts sequence/frame 1 at offset zero without mutation |
| Binding validation | Strict lowercase 64hex target; input payload binding empty; geometry payload binding valid; only input/geometry kinds |
| Control identity | Full target, stable binding, kind, nonce, revision and monotonic expiry all validate and participate in equality |
| Active state | Missing binding/current, inactive state, foreign target and noncurrent tuple refuse |
| Monotonic expiry | Positive time strictly before expiry accepts; deadline equality, later time and nonpositive clock refuse |
| Byte bounds | Payload 1..131072 and request 1..65536; offset and remaining range checked before arithmetic |
| Initial numbering | Attempt/frame gaps, nonpositive sequence and unexplained offset refuse |
| Partial completion | Only exact accepted-prefix continuation with the next attempt sequence accepts |
| Same-frame identity | Changed digest or length refuses; changed control requires a strictly higher current revision and unchanged stable binding/kind |
| Renewed known suffix | Fresh current lease with higher revision and rotated nonce/full target continues only at the known accepted prefix; replay, changed payload, sequence gaps, lower/equal changed revision and frozen outcomes refuse |
| Next frame | Full completion admits only the next frame at offset zero, including newly current revision |
| Attachment rotation | A higher revision may change the full attachment target after frame completion while preserving stable binding; changed current or retained binding refuses |
| No bypass or replay | An unfinished frame cannot be skipped; a completed frame cannot restart |
| Frozen outcome | Pending flag, Queued status or Unknown status prevents further attempts |
| Retained receipt bounds | Invalid prior offset, payload/request bounds, accepted prefix and exhausted counters refuse before overflow |
| Geometry | Exact bound payload may continue within frame 1; payload substitution and frame 2 refuse |

Binding target digests identify the stable adopted runtime and pane. Controls
carry both that `binding_digest` and a full `target_digest` that includes client
and attachment generation. A fresh current lease may rotate the full target and
nonce during a partially completed frame only with a strictly higher revision,
unchanged stable binding and kind, and identical payload digest and length. It
authorizes only the exact known suffix after the prior Completed receipt; it
does not replay the accepted prefix. The next attempt sequence and contiguous
offset remain mandatory. Queued and Unknown outcomes freeze renewal, and a
fully completed frame cannot restart. The unchanged current control may also
continue its exact suffix. The native owner preserves the old attempt tuple
until a new native submission records the renewed attempt.

The native owner remains responsible for live issuance, revision installation,
revocation, locking, and actual write outcomes. A successful pure reason helper
returns an empty string indicating consistent metadata, never permission to
write. Fabricated pure-state fixtures never authorize IO; the native owner
produces receipts from real completions. Completed means that an individual native attempt has a known accepted
prefix; frame completion requires the cumulative prefix to reach payload size.
