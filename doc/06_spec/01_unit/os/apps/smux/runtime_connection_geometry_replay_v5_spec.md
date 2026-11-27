# Geometry request replay and lease renewal V5

Status: **AUTHORED SOURCE-ONLY NOT_RUN**. No tests, builds or native operations
were executed. Authoring these specs did not modify the production helper; that helper is part of the reviewed lease-renewal correction.

Source: `src/os/apps/smux/runtime_connection_geometry_replay_v5.spl`.
Spec: `test/01_unit/os/apps/smux/runtime_connection_geometry_replay_v5_spec.spl`.
The actual `SmuxConnectionGeometryV5.begin` consumer calls this production pure
helper; the specs invoke that same helper directly with public metadata.

`true` means return retained replay/observation without a new begin. `false`
means a next metadata candidate, never permission, issuer validation or a native
completion. `unresolved = true` represents the caller's Unknown/in-flight
classification; no native Unknown receipt is fabricated by these fixtures.

| Authored case | Intended assertion |
|---|---|
| New revision restarts | Known revision 3 sequence 5 followed by revision 4 sequence 1 returns false |
| Exact replay | Identical same-lease/same-attempt metadata returns true even while unresolved, allowing observation only |
| Changed payload | Valid changed geometry wire digest/dimensions at the same attempt refuses |
| Same-lease next | Only exact next sequence admits a candidate after known completion; unresolved and gaps refuse |
| Renewal sequencing | New revision with old counter plus one refuses; renewed sequence 1 still cannot bypass unresolved prior ownership |
| Same/lower mutations | Changed nonce, full attachment target, expiry or issue time cannot relabel a revision; lower revision refuses |
| Attachment rotation | Higher revision permits client/attachment rotation while preserving stable binding; unresolved still blocks begin |
| Stable binding | Changed pane, runtime, pod or adopted binding/service/session/window/epoch/child metadata refuses even at higher revision |
| First request and bounds | No-history sequence 1 admits a candidate; other initial sequences, nonpositive/above-cap integers and unresolved state refuse appropriately |

Fixtures reuse the existing public pure Windows adapter scope/workload fixture,
construct public target/Geometry lease metadata and hash actual production
resize wire bytes. They do not create an opaque owner, actual adoption, native
receipt, authenticated issuer or capability. Live lease validation, actual
rights, native begin/observation and cleanup remain outside this pure helper.
The largest permitted metadata revision case does not claim a real issued lease.

These authored cases describe source behavior only. They provide no executable
positive native coverage, race witness, branch-coverage measurement or Windows
qualification, and require Astra joint review before any freeze admission.
