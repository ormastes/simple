# Podman primary attach V1

Status: source implementation; AWAITING_VERIFICATION. No live Podman, native
controlled-input, or SSpec qualification is claimed by this document.

## Request and creation

The existing canonical Linux request binds `terminal_mode` into its semantic
digest before the provider journal admits an effect. `stdin` requests create
with `--interactive`; `tty` requests add `--tty`. `none` retains its existing
command and behavior. Only an explicitly configured managed Podman provider
admits these modes. Docker/runc and unconfigured legacy providers refuse them.
No shell command is constructed. Environment, image, resource and exact native
identity checks remain those of the existing provider.

The selected-containment route remains unsupported in this slice. The separate
held configured-containment draft and closed durable exec state machine are
not dependencies of this feature.

## Actual eligibility and immutable plan

Planning uses the shared Simple Container API and returns the updated owner,
including on error. The Linux adapter checks the retained request and exact
runtime identity, refreshes the installed engine observation, then queries the
exact full native ID. A bounded strict response must contain the same ID and
all five ownership labels, running status, `Config.OpenStdin=true`, and
`Config.Tty` equal to the signed mode. These are configuration observations;
they do not prove a primary process incarnation or attachment success.

The distinct `ContainerPrimaryAttachPlanV1` binds the workload, runtime,
target-binding identity, helper resources, policy, mode and canonical native
launch template. Its provider-derived argv is `attach`, `--no-stdin=false`,
`--sig-proxy=false`, `--detach-keys=`, and the full native ID. The empty detach
setting disables key interception; it is a single typed argument.

Opening rederives the canonical plan under fresh observations and compares
the complete encoding. The original helper intent, reservation operation,
prepared receipt, parent budget and launch deadline must match the shared
admission checker. The provider performs another eligibility observation
immediately before submitting the owned helper launch. Changed configuration
or policy refuses admission; observations do not reserve future runtime state.

## Stream and control ownership

The canonical group-process owner supplies the only stream reader and cleanup
authority. `Ready` means that an owned helper bundle is available, not that
Podman attached or the application is running. All cleanup-bearing outcomes
are retained. The common session constructor must install and verify the
irreversible controlled-input latch before publishing a session. No raw bundle
is published to an application as an interactive capability.

Live input also requires the actual authenticated control issuer, exact target,
revision, nonce, expiry and native sequence checks. A helper lease or copied
plan is not input authority. Geometry requires a separate actual provider
resize path; this checkpoint does not implement one. EOF and helper cleanup
do not prove workload exit or release container capacity. Helper accounting
remains separate from the already charged container.

## Evidence and remaining acceptance

Focused source scenarios cover exact argv, both creation modes, actual common
planning with returned owner state, immutable request/config/label mismatches,
helper-chain refusal and the scripted provider's native-spawn prohibition.
All scenarios are authored, NOT_RUN. A scripted fixture cannot create a native
handle or qualify the installed runtime.

Required runtime acceptance still includes real image stdin/TTY behavior,
fresh output nonce through the sole pane reader, actual controlled input and
revocation, disabled detach keys, helper cleanup without workload stop, and
independent exact-container inspection. Resize and exact exec attachment are
separate capabilities. The finite CLI observations can block for their capture
and hashing phases; repeated fresh observations do not constitute an
asynchronous or hard wall-clock bound.

Pinned Podman v5.2.5 sources: `docs/source/markdown/podman-attach.1.md.in`,
`docs/source/markdown/options/detach-keys.md`, and
`libpod/container_inspect.go`. Their documented flags and actual inspection
field assignments support the source mapping, not live conformance.
