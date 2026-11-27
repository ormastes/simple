# Container byte handoff correlation codec

Executable source: `test/01_unit/lib/common/contracts/container_byte_handoff_v1_spec.spl`.
Status: **NOT_RUN**. Six source cases; no runtime or authenticated handoff claim.

| Case | Required observation |
|---|---|
| Canonical roundtrip | Every field survives, with independent provider and source generations. |
| Binding mutations | Changing any of the eight correlation fields rejects the original digest. |
| Invalid generations | Zero provider generation and negative source generation are rejected. |
| Malformed identity | Pathlike operation IDs, uppercase nonce, scope text in gateway nonce, and changed binding are rejected. |
| Canonical bounds | Leading/trailing padding, appended data, and input over 4096 bytes are rejected. |
| Strict fields | Missing, unknown, duplicate and wrong-typed fields are rejected. |

The codec never creates a native endpoint or authenticated gateway context.
Native tests must independently prove one-use descriptor consumption, peer UID
binding, stale-generation rejection, truncated/extra-FD cleanup, and retained
Host ownership after publication uncertainty. These are not established by a
successful metadata roundtrip.
