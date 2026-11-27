# Windows broker bounded binary frames

Status: **SOURCE-ONLY NOT_RUN**. These authored cases call the actual pure codec
and incremental reader. No Windows IO, authenticated parent connection, control
issuer, native barrier, Engine request or broker process was exercised.

Source: `src/lib/nogc_async_mut/container/providers/windows/docker_broker_frame_v3.spl`.
Spec: `test/01_unit/lib/nogc_async_mut/container/windows_docker_broker_frame_v3_spec.spl`.

| Requirement | Executable cases and intended assertions |
|---|---|
| REQ-WBF-001: preserve binary bytes and exact retained correlation | Non-UTF8 body roundtrip and canonical re-encoding; changed region, generation, direction or invalid expected context refuses |
| REQ-WBF-002: bound accumulation before allocation | Every header/body split; one-frame consumption from coalesced input; oversized or negative announced length retains header-only storage; oversized chunks and truncated headers refuse |
| REQ-WBF-002: classify EOF honestly | Every partial prefix fails at EOF; complete/empty reader accepts EOF; subsequent data refuses |
| REQ-WBF-003: canonical bounded metadata | Unknown, duplicate, missing, mistyped, wrong-version and noncanonical SDN refuse; invalid metadata UTF8/length and changed body with recomputed outer checksum refuse |
| REQ-WBF-004: enforce operation-specific data shape | Input prefix, geometry digest/dimensions, progress flags and complete-prefix correlation; output offsets, empty output and EOF constraints |

The outer binary envelope is the existing process transfer codec. Its payload is
bounded to 65536 bytes before full decode: eight-byte metadata length, canonical
SDN UTF8 metadata at most 4096 bytes, then raw binary body at most 61432 bytes.
No body data passes through text or hex conversion. SHA256 and the outer checksum
check integrity only. The reader accepts expected correlation from its caller;
the real caller must derive it from retained authenticated launch context.

Direction permits input/geometry only Parent-to-Process and progress/output only
Process-to-Parent. These values reference existing control target, revision and
nonce metadata; they are not a new lease or proof. Parsing does not authenticate
the parent, create a live control projection or authorize native IO. Large Engine
output requires ordered chunks and the separate output progress tracker.

The runtime fixture, exact authenticated startup, installed-root reopening,
native revision/expiry/attempt gate and positive writable session remain required
integration and qualification work. The current Engine exchange stays GET-only.
