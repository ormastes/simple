# Operation checkpoint codec — authored manual

Status: **NOT_RUN / NOT_GENERATED / NOT_QUALIFIED**, 2026-11-15.

Source: [distributed_operation_checkpoint_v2_spec.spl](../../../../../../test/01_unit/lib/common/task_runner/distributed_operation_checkpoint_v2_spec.spl).
This manual describes executable source assertions. It is not runner output,
coverage evidence, a generated-manual review, or a verification PASS.
The canonical `bin/release` runtime is absent; no build, seed, runtime or test
was invoked during this continuation.

| Scenario | Required observation | Evidence |
| --- | --- | --- |
| Independent golden bytes | Exact operation page, endpoint page and manifest match literal field order, quoting and LF; decoded envelope and history retain their values | NOT_RUN |
| Numeric-only digest | Actual generic WAL control quotes a decimal-looking SHA-256 string and its measured size includes quotes and LF | NOT_RUN |
| Strict schema and framing | Extra LF, duplicate keys, noncanonical integer spelling and unknown manifest field reject | NOT_RUN |
| Page integrity | Same-length changed page fails its digest; missing object propagates its actual error | NOT_RUN |
| Semantic bindings | Terminal outcome without digest and missing enclosing endpoint reject; key ordering follows UTF-8 bytes | NOT_RUN |
| Bounds before reads | Exhausted endpoint count and maximum-i64 page byte count reject before the object callback is permitted | NOT_RUN |

The codec fixture is plain data, never a fabricated journal or native owner.
Expected golden bytes use explicit spelling and the existing envelope format,
not the checkpoint encoder as their oracle. The unit cases do not qualify
publication, concurrent writers, power-loss durability, Windows native exports,
large-page performance or physical reclamation. The full owner feature has an
[owner-health implementation awaiting independent review and execution](../../../../../03_plan/agent_tasks/daemon_operation_retention_owner_health_v2.md).
