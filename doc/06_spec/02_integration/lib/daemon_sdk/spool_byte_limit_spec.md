# Daemon spool serialized byte limits

Requirement: DAE-01, HOST-01. Authored manual; not generated execution evidence.
Spec: `test/02_integration/lib/daemon_sdk/spool_byte_limit_spec.spl`.
SSpec execution: NOT_RUN (admitted self-hosted compiler unavailable).

| Scenario | Action | Required observation |
| --- | --- | --- |
| Request boundary | Write fixed envelope totaling 1 MiB, then another totaling 1 MiB + 1 | Exact-size file has 1,048,576 raw bytes and decodes faithfully; oversized publication refused |
| Response boundary | Repeat with fixed response envelope | Same acceptance/refusal, including complete decoded payload |
| Multibyte bound | Write 2^19 two-byte UTF-8 scalars plus framing | Both writers refuse; neither final message path exists |

All scenarios use actual provider/file APIs and private temporary roots. Directory
creation before size rejection is allowed. Tests do not depend on current text
len semantics; they protect the planned character-count migration. No pre-fix
failure is claimed without running that migration. See
`doc/05_design/daemon_spool_byte_limit_2026_11_07.md` for review and diagnostic status.
