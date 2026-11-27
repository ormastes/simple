# Linux OCI trusted local administrator engine policy

Status: **AWAITING_VERIFICATION**. This is an authored manual mirror of
`test/01_unit/lib/nogc_async_mut/container/providers/linux/oci_engine_policy_spec.spl`,
not generated execution evidence. All focused cases remain UNEXECUTED.

| Scenario | Assertion scope |
|---|---|
| Roundtrips canonical policy bytes and binds ordered storage options | Canonical SDN roundtrip and semantic/order digest changes |
| Refuses unknown, noncanonical, oversized, and deeply nested policy data | Strict schema and bounded parsing before interpretation |
| Rejects unsupported modes, paths, and option aliases before native observation | Explicit mode selection, absolute scoped paths, rejection of `/podman` through policy and production constructor before observation, valid `/usr/bin/podman` control, duplicate option keys |
| Rejects setuid, setgid, writable, and nonexecutable metadata | Live-used metadata predicate checks each permission bit and UID ownership |
| Routes exact scoped argv and explicit empty storage options | Independent complete argv, local mode, roots/driver/options, literal values |
| Observes exact local rootless UID, roots, driver, version, and binary digest | Typed observed fields and refusal of mismatched scope |
| Rejects duplicate, malformed, missing, and excessive-depth JSON | Strict external JSON plus byte/depth bounds |
| Matches scalar options and upstream overlay mount-program object | Exact scalar/value mapping and helper metadata changes affect identity |
| Refuses unobservable option object forms | No guessed generic nested-object coercion |
| Executes exact scripted absolute route and reports identical selected command | Real provider request consumer, full expected argv, truthful command receipt |
| Retains baseline and refuses changed executable before effect consumption | Changed observation does not advance retained baseline or consume native-effect fixture |

The scripted seam substitutes engine observation/effect results explicitly for
unit fixtures. It does not prove filesystem metadata acquisition, actual engine
behavior, rootless launch, output delivery, or production enrollment. The native
observer uses retained file metadata/hash and bounded scoped engine info in the
production path; these operations still require executable qualification.

Pending verification: run this spec and existing provider lifecycle, binding,
codec, command mapping, and CI backend-selection regressions using an admitted
self-hosted runtime; complete core/library/MCP smoke and SPipe evidence gates;
then run a real installed rootless Podman matrix with approved executable/store
policy, a locked local image, immutable request journal, independent native-ID
inspection, known output, and exact owned cleanup. Host CLI wiring and the
provider output-only attach owner are not implemented by this slice. Interactive
stdin, resizing, and terminal readiness remain separate blocked requirements.

No build was started: the campaign's unchanged `fill_span` producer failure and
absence of Podman remain blockers. Source guards and a draft PR must not be
reported as a runtime test PASS. All future verification jobs require root's
allocation within the shared five-CPU limit.

Execution-options source update (UNEXECUTED): Podman create vectors now include `--http-proxy=false`; typed environment/cwd are admitted, terminal effects remain refused. See `doc/05_design/oci_execution_options_effects.md` and the eleven-case system specification mirror.
