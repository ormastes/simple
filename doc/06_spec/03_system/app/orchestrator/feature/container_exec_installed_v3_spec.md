# Installed exec carrier integrity

Status: **NOT_RUN / AWAITING_VERIFICATION**. Four authored scenarios exercise
the actual pure matcher. They do not perform signed installation, native IO,
Podman exec or a production capability grant.

Source: `test/03_system/app/orchestrator/feature/container_exec_installed_v3_spec.spl`.

| Scenario | Prevention evidence authored |
| --- | --- |
| Original artifact, scope and baseline | Canonical installation artifact matches the exact signed child bindings; CLI and composite control pins remain distinct. |
| Artifact or policy mutation | Changed artifact hash, policy bytes and policy hash are rejected. |
| Consistent but foreign installation | Rehashed alternate service scope, provider generation and baseline are rejected against the original child intent. |
| Control pin substitution | Substituting the composite control pin for the original CLI baseline is rejected. |

The carrier has no decoder. Its matcher reuses canonical installation encoding
and the common retained-admission binding matcher. Structural integrity is not
proof of a completed Host journal entry: only the production completed signed
installation loader may project this carrier into the trusted exec composition.
The actual provider must still observe and compare the installed service,
runtime parent and control pin before effects. Fresh grant expiry remains a
separate native submission check; retained bindings do not renew it.
