# Exact configured containment inspect

AUTHORED / NOT_RUN. Five pure source scenarios; no native acceptance.

- Typed container-only inspect query with full lowercase 64-hex ID; option/name/partial IDs refused. The entire runtime Go template must equal an independent raw-string golden.
- Nested range/if/end actions preserve all 22 literal Go delimiter pairs and the separate final JSON object brace.
- Exact running identity, selected profile, positive PID and owned canonical cgroup accepted as configuration data.
- Correlation labels, runtime/manager/namespaces/cgroups, privilege, capability counts, no-new-privileges, read-only root and PID mutations refused.
- Unknown/duplicate/nested/trailing fields and missing/duplicated no-new-privileges rendering refused.

Pinned Podman v5.2.5 define/container_inspect.go (240b09...) and container_inspect.go (ef4bac...) supply the inspected fields. Cgroups enabled is reported as default. EffectiveCaps/BoundingCaps describe OCI spec configuration, not measured native capabilities. The returned PID/cgroup is metadata requiring independent native validation before further authority. No lifetime or teardown proof is established.

The brace regression replaces ordinary-string substring needles, which collapsed
just like the defective production literal and could mask the error. The new
expected template is raw text; it cannot undergo the same ordinary-string brace
collapse. The production fix changes only the template escaping, preserving the
same nineteen fields and all strict parser/security/identity refusals.

Both new assertions and the three unchanged payload scenarios are **NOT_RUN**.
Compiler/native/Podman execution was not attempted; the prior qualification cap
remains exhausted. Reachability and source evidence are recorded in
`doc/08_tracking/bug/containment_inspect_brace_escape_20261115.md`. This does not
qualify native containment or change the separate fresh/common fixed queries.
