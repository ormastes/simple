# CI container backend selection

`probe_container_lane(engine: text = ENGINE_PODMAN)` probes only the selected
backend. `run_pipeline(pipeline, templates, run_id, engine: text = ENGINE_PODMAN)`
passes the same selection through its cached per-run probe to the existing
`LinuxOciRuntimeProviderV1`; it adds no execution framework. This runner has no
production CLI caller.

The default invocation is `run_pipeline(pipeline, templates, run_id)`.
Explicit Docker configuration is
`run_pipeline(pipeline, templates, run_id, ENGINE_DOCKER)`.
Missing Podman blocks the default container lane even if Docker is installed.
Unsupported selections, including `runc` and `auto`, reject before pipeline
expansion, boot identity reads, or job execution. `ENGINE_RUNC` remains a legacy
name, not a supported selection. Process-only pipelines avoid backend probes.

The live probe validates the selection before executing any client and observes
only that selected client's availability. It uses
`container_engine_selection_error` to decide whether absence blocks the lane.
This pure decision function accepts separate observed client availabilities so
tests can cover absent Podman with present Docker without changing PATH or
launching a fake engine. An empty selection error proves only that policy allows
the selected client; namespace/subordinate-ID or Docker daemon checks and the
provider's own probe still apply. It is not runtime qualification.

`test/02_integration/app/ci/container_backend_selection_spec.spl` covers explicit
selection, missing clients, unsupported selections, and rejection before an
invalid pipeline is expanded. The existing runner spec now requires any default
probe success to name Podman. No image pulls or runtime mutation are required by
the new selection spec.

Runtime validation is pending: the admitted self-hosted runtime and Podman are
absent on the current host. Source review is not a passing runtime test or
container qualification receipt. Parent lane owns final verification and landing.

## Remaining integration

This scope preserves the release-base provider and does not copy the unrelated
provider changes in the main worktree. `ContainerV1` still lacks environment,
working-directory, and workspace fields. The main worktree has typed provider
command/options/mount/attach helpers, but wiring them into the schema and CI
runner remains separate work. CI also does not yet select `replace_entrypoint`
to implement the declared Kubernetes `command` semantics. Backend selection
does not resolve those execution-contract gaps or establish CI readiness.
