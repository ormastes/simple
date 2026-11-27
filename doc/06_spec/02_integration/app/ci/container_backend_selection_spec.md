# CI container backend selection

Source: `test/02_integration/app/ci/container_backend_selection_spec.spl`.

Status: **UNEXECUTED**. This is an authored source mirror, not generated runtime
evidence. The admitted self-hosted runtime is unavailable; no container runtime
qualification is claimed.

| Scenario | Observation and required result |
| --- | --- |
| Missing default Podman | Podman absent, Docker present: selection error names missing Podman. |
| Explicit Docker | Podman absent, Docker present: Docker client selection allowed. |
| Missing explicit Docker | Podman present, Docker absent: selection error names missing Docker. |
| Selected Podman | Podman present, Docker absent: Podman client selection allowed. |
| Unsupported names | `runc`, empty name, `auto`, uppercase and arbitrary executable: rejected; public probe returns unavailable with no engine or privilege claim. |
| Early pipeline rejection | Unknown backend with a missing job template: backend rejection precedes pipeline expansion. |

The availability observations exercise the policy function used by the live
probe. Allowing a client selection does not prove daemon reachability,
rootless capability, provider admission, or successful execution. The public
unsupported-name probe rejects before invoking a client. No test invokes a
shell, pulls an image, or prunes runtime state.
