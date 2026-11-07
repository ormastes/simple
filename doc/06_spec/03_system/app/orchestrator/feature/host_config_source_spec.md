# Direct HostConfig source boundary

Source: `test/03_system/app/orchestrator/feature/host_config_source_spec.spl`.
Status: **NOT_RUN**. Authored manual, not generated execution evidence.

Decode valid indented and canonical configuration with numeric10000 preserved. Reject malformed source, duplicate/unknown fields, wrong kind, invalid event bounds and multibyte input beyond1MiB bytes. Schema validity grants no host admission.

The compiled CLI path or fixture must exist before executing the test. No build,
admitted SSpec, compiler qualification, provider execution or authentication PASS
is claimed. Missing executable/fixture produces real assertion failure.
