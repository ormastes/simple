# Numeric user selection V3

Source: `test/01_unit/lib/nogc_async_mut/container/providers/linux/oci_user_selection_v3_spec.spl`.

Five authored scenarios, UNEXECUTED. Frozen historical golden digest constants were independently derived from the prior canonical digest algorithm; they are assertions to execute, not reported runtime results.

Golden provenance: the V1/V2 hashes were computed once with Python `hashlib` from the pre-edit canonical scalar order at base `7a44d97b685`. Literal SDN fixtures were derived from that base's canonical encoder, including field ordering and final newline. Neither derivation is evidence from an admitted Simple runtime; the executable assertions remain pending.

| Scenario | Oracle |
|---|---|
| Backward compatibility | Literal historical V1/V2 codec bytes and frozen hashes remain exact with absent selection. |
| V3 codec | UID/GID/keep-id roundtrip; downgrade, tampering and missing fields reject. |
| Selection limits | Partial, negative, overflow and unsupported mode/backend refuse; supported numeric endpoints parse. |
| Typed create | Independent complete Podman argv contains numeric UID:GID and keep-id. |
| Bound replay | Actual common create rejects changed UID/GID or removed selection before a second executor effect. |
