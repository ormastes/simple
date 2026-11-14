# smux primary V4 request

Source: `test/01_unit/os/apps/smux/runtime_primary_request_v4_spec.spl`.
Status: **NOT_RUN**. Manually authored companion, not generated execution evidence.

Six scenarios assert canonical roundtrips for both modes and full-width target
fences; V3 incompatibility and whole-request digest binding; unknown, duplicate,
missing, and mistyped fields; ordering, shape, and size refusal; delegated target
validation and unsupported modes; strict bounded base64url tokens.

These are pure request-byte checks. They neither admit a helper nor open a
provider or native session. The server's total frame bound remains separate.
