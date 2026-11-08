# Full runtime-operation codec V2

Status: **NOT_RUN** — source-authored manual; no compiler, unit suite or provider
was executed. Source:
`test/01_unit/lib/common/contracts/container/runtime_operation_codec_v2_spec.spl`.

| Scenario | Intended assertion |
| --- | --- |
| Full roundtrip | Command/program/ordered argv, state/full identity, CLI exit zero versus workload exit 17, UTF-8/multiline stdout/stderr/reasons and canonical bytes survive. Existing observation digest is unchanged. |
| Empty refusal | Rejected/unknown empty observations roundtrip as data and still cannot satisfy the existing observation-digest identity contract. |
| Root schema | Unknown, missing, duplicate and incorrectly typed fields reject. |
| Nested schema | Nonobject command, nontext argv and injected identity fields reject. |
| Bounds and framing | Other version, missing/excess newline, input above 2 MiB, oversized stdout and more than 4,096 argv entries reject. |

Encoding/decoding grants no provider authenticity, execution or cleanup authority.
Runtime behavior, branch coverage and performance remain unverified.
