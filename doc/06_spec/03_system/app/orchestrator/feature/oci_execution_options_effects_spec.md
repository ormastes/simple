# OCI execution options effects specification

Source: `test/03_system/app/orchestrator/feature/oci_execution_options_effects_spec.spl`.

Status: manually authored source mirror, UNEXECUTED. Scripted command assertions exercise actual implementation branches; they do not qualify native Podman.

| Scenario | Assertion |
|---|---|
| Literal typed options | Explicit cwd and NAME=VALUE argv preserve metacharacters, newline and empty value. |
| Podman create | Independent full argv includes proxy inheritance suppression and literal empty arguments. |
| Docker compatibility | Independent full argv admits options without a Podman-only flag; runc refuses. |
| Invalid environment | Duplicate names, malformed name and NUL reject before state reservation/executor. |
| Invalid cwd | Relative and noncanonical paths reject. |
| Common action projection | Actual common facade reports exact argv/cwd and no invented mounts. |
| Command-only override | Explicit executable produces no inherited image CMD tail. |
| Unresolved defaults | Image entrypoint, implicit cwd and generic bundle workspace cannot produce a projection. |
| Fixed build mounts | Real read-only input/writable output mappings preserve spaces and Unicode. |
| CSV root safety | Ambiguous/noncanonical build roots reject both admission and effect construction with zero executor attempts. |
| Bound replay | Changed env/cwd digest rejects before a second common create effect. |

Prerequisite: common facade integration of `simple_container_action_project_v2`. No test/build/check was run for this source slice.
