# Strict remote policy decoder V1

Status: **AWAITING_VERIFICATION** — source-authored manual; no compiler, seed,
test runner or real workspace policy read was executed.

Source: `test/01_unit/app/buildrunner/remote_policy_codec_v1_spec.spl`.
Implementation: appended `remote_policy_decode_v1` in
`src/app/buildrunner/remote_evidence_v1.spl`.

The decoder accepts the existing `SIMPLE-REMOTE-POLICY-1` canonical line wire.
It requires a final newline, no trailing fields, at most 1 MiB and at most
12,300 split fields. Case and tool counts are each bounded at 4,096; the
existing policy validator also requires at least one tool and, for test
policies, at least one expected case and a valid report path. Evidence memory
budget remains bounded at 256 MiB. All integer fields use canonical decimal
without signs or leading zeroes. A checked epoch parser preserves the existing
encoder's full positive i64 range and rejects overflow before multiplication.

After parsing, the existing encoder performs semantic validation and the
decoder requires re-encoded bytes to equal the original payload. The decoded
policy remains untrusted until the task's pinned policy-input digest and the
remaining authority/execution checks accept it.

| Scenario | Intended assertion |
| --- | --- |
| Golden and roundtrip | An independently specified test-policy wire matches; build and test policies preserve every field and re-encode identically. |
| Epoch and path compatibility | Maximum positive i64 epoch and a percent-bearing UTF-8 tool path roundtrip. |
| Framing | Unknown version, missing terminator, truncation and trailing fields reject. |
| Epoch strictness | Leading zero, explicit sign, zero and values above i64 reject. |
| Numeric bounds | Over-budget memory, zero memory, excessive case/tool counts and noncanonical memory integer reject. |
| Semantic validation | Duplicate expected cases, unsafe tool paths, duplicate tools and unsupported scalar escaping reject. |
| Transport limits | Input above 1 MiB and excessive line count reject before policy construction. |

This decoder performs no file I/O, process launch, test execution or publication.
Execution, performance and integration remain unverified; no PASS is claimed.
