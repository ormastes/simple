# Linux primary geometry HTTP V1 codec

Source: `test/01_unit/lib/nogc_async_mut/container/providers/linux/primary_geometry_http_v1_spec.spl`.
Status: **NOT_RUN**. Eight source-only scenarios, manually authored companion.

The scenarios cover exact direct container GET inspect and POST resize paths,
lowercase full IDs, dimension/area bounds, pinned HTTP 200 empty resize responses
with optional Content-Type, strict shared response framing, real direct inspect
JSON shape and all five retained labels, running/OpenStdin/Tty correlation,
duplicate/type/missing/depth/byte/structural bounds, and preserved exec/info
response action contracts following neutral framing extraction.

Resize framing requires Content-Length or strict chunked termination. Both
forms reject extra bytes, conflicting framing, duplicate headers, incomplete
payloads, and chunk trailers. Inspect requires application/json and a direct
object, bounded to 1 MiB, nesting depth 16, and 16384 structural delimiters.
Unknown inspect fields remain allowed for the real engine document.

Pinned source contract: [Podman v5.2.5 ResizeTTY](https://github.com/podman-container-tools/podman/blob/v5.2.5/pkg/api/handlers/compat/resize.go)
and [container route registration](https://github.com/podman-container-tools/podman/blob/v5.2.5/pkg/api/server/register_containers.go).
The container branch uses AttachResize and HTTP 200 with an empty body;
HTTP 201/204 and exec/start response conventions are refused for this action.

Synthetic wire/JSON fixtures supply codec inputs only. No socket connects,
native TTY ownership, applied geometry, live engine observation, effect receipt,
or successful cleanup is exercised or claimed. The native campaign remains
closed; runtime/build/test execution is NOT_RUN.
