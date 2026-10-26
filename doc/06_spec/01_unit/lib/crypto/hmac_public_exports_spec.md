# Public HMAC byte exports

Requirement: REQ-HMAC-PUBLIC-BYTES-001.
Executable: `test/01_unit/lib/crypto/hmac_public_exports_spec.spl`.
Status: Simple execution UNRUN. Oracle bytes independently checked with .NET.

| Scenario | Real operation | Required assertion |
| --- | --- | --- |
| Public SHA384 import | Call `std.crypto.hmac.hmac_sha384_bytes` with twenty 0x0b key bytes and ASCII `Hi There` | 48 bytes and exact fixed known-answer hex |
| Public SHA512 import | Call `std.crypto.hmac.hmac_sha512_bytes` with the same inputs | 64 bytes and exact fixed known-answer hex |

The public import itself reproduces the missing-export defect before repair.
Both cases must execute, with no skipped/dropped cases; file-load success alone
is insufficient. This forwarding repair does not change HMAC algorithms,
allocation, or ABI. Full TLS behavior and compiler bootstrap are separate gates.
