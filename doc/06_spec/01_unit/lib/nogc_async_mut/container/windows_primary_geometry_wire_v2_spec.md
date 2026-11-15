# Pure Windows primary geometry wire metadata V2

Status: **AUTHORED SOURCE-ONLY NOT_RUN**. No tests, builds, native IO or actual
geometry effects were executed.

Source: `src/lib/nogc_async_mut/container/providers/windows/primary_geometry_wire_v2.spl`.
Spec: `test/01_unit/lib/nogc_async_mut/container/windows_primary_geometry_wire_v2_spec.spl`.

The fixtures reuse the public pure Windows adapter workload/scope fixtures,
canonical direct-plan constructors and public Geometry lease/target metadata.
They create no opaque connection owner, adoption, verified grant or receipt.

| Authored case | Intended assertion |
|---|---|
| Exact wire/control | Production HTTP resize serialization matches exact method, native container ID, query geometry, headers and empty body; full wire hash and stable/full target fields bind the output |
| Attachment rotation | Matching client/attachment changes preserve stable binding and wire while changing the full control target digest |
| Plan/target match | Stale self-digest, foreign runtime and changed lease target refuse with exact errors |
| TTY requirement | A valid canonical stdin plan refuses geometry |
| Kind/principal/nonce | Input kind and changed principal/raw nonce refuse through the actual Geometry lease checker |
| Nonce bound | Exactly 256 raw nonce bytes accept with matching hash; empty or oversized nonce refuses |
| Nanosecond deadline | Largest safe millisecond deadline converts exactly; nonpositive or overflow-inducing values refuse before multiplication |
| Lease timing | Expired, not-yet-valid and malformed windows refuse |
| Full-wire digest | A stale dimension or digest of another representation cannot bind the wire; malformed digest refuses |
| Common geometry bounds | Dimensions, area, attempt and revision retain shared request-check limits |

The builder uses API version `1.48`, actual `windows_engine_container_resize_v3`
and `windows_docker_engine_exchange_serialize_v3`. The payload digest covers
every HTTP wire byte, not merely the geometry values. The returned Geometry
binding identifies the stable adopted runtime/pane and full wire digest; control
also carries the full current target, nonce hash, revision and bounded deadline.

All results remain metadata. Successful construction neither establishes actual
adoption nor validates a live issuer, installs native control, acquires a pipe,
writes bytes or proves a resize. Those checks and actual native IO belong to
the separate retained-owner factory. These pure cases make no Windows native
qualification or production-readiness claim.
