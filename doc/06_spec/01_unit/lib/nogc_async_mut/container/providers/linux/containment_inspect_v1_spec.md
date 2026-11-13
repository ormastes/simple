# Exact configured containment inspect

AUTHORED / NOT_RUN. Four pure source scenarios; no native acceptance.

- Typed container-only inspect query with full lowercase 64-hex ID; option/name/partial IDs refused.
- Exact running identity, selected profile, positive PID and owned canonical cgroup accepted as configuration data.
- Correlation labels, runtime/manager/namespaces/cgroups, privilege, capability counts, no-new-privileges, read-only root and PID mutations refused.
- Unknown/duplicate/nested/trailing fields and missing/duplicated no-new-privileges rendering refused.

Pinned Podman v5.2.5 define/container_inspect.go (240b09...) and container_inspect.go (ef4bac...) supply the inspected fields. Cgroups enabled is reported as default. EffectiveCaps/BoundingCaps describe OCI spec configuration, not measured native capabilities. The returned PID/cgroup is metadata requiring independent native validation before further authority. No lifetime or teardown proof is established.
