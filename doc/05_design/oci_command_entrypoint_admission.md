# OCI executable override and CI request mapping

Status: source admission, **UNEXECUTED** runtime evidence. Base:
`6c1e9968f374`, the reviewed request-binding foundation. No schema or digest
format changes are included; the existing `replace_entrypoint` field already
participates in immutable payload binding. This slice reuses the Linux OCI
provider and its journal owner, without another execution framework.

## Provenance and scope

The existing dirty main command helper was identified with source SHA256
`ed48e7119a0aa5075d011f8772ecca0f88428d9860425594bf858cca1c2d8128`.
The hardened parked helper admitted here has SHA256
`5fecf529ef2e9b77562bb3473e6645ae39eaea4dc9ca3f943a89b79f447fd883`.
Only the helper, its tests, and the agreed CI request construction seam were
restored from parked work. The parked provider was never restored; provider
changes are surgical on top of the reviewed binding foundation. Unrelated dirty
main files remain untouched.

## Mapping

`oci_command_parts_v1` returns existing typed `OciCommandPartsV1` options and
workload arguments. False mode retains positional `command + args` after the
image. True mode emits the scalar option pair `--entrypoint`, `command[0]`
before the image, followed by `command[1:] + args` as distinct workload argv.
No splitting, joining, shell interpolation, or implicit shell is introduced.

The live CI runner calls
`ci_container_request_v1(name, container: ContainerV1, run_id)`, which selects
true mode exactly when `container.command` is nonempty. Empty command keeps the
image ENTRYPOINT, including args-only requests. This describes executable
mapping, not full Kubernetes image-default CMD equivalence or shell expansion.
An image's default arguments remain engine/image behavior requiring later live
conformance evidence.

Build mode continues to select an executable override with its existing
read-only input and writable output mounts in the same order. An empty build
command retains the `build-command-empty` error. The standalone bare-runc builder
explicitly rejects the new override instead of silently ignoring it; the live
provider already refuses unqualified runc lifecycle execution.

## Refusal and literal values

The helper rejects NUL in command or args, an empty selected executable, a
trimmed executable beginning with `-`, and JSON-shaped selected executable text
(trimmed text beginning `[` or equal to `null`). Trimming is used only to detect
these refused forms; accepted executable bytes are returned unchanged. Spaces,
metacharacters, empty workload values, and option-looking workload arguments
remain literal argv elements. Effective override mode, explicit or build, allows
empty command-tail arguments; legacy false/nonbuild mode retains its existing
empty-command-element validation.

This conservative scalar subset avoids ambiguity because
[Podman documents JSON entrypoint arrays](https://docs.podman.io/en/latest/markdown/podman-create.1.html),
while [Docker describes an executable string and positional arguments](https://docs.docker.com/engine/containers/run/).
These references informed source validation; they are not native conformance
evidence. Provider validation and standalone construction both call the helper
before any native create. Foundation request bounds also reject NUL before
logical preparation and binding.

## Replay and remaining effects

The reviewed binding owner remains authoritative. Same-bound replay can reuse
the existing attempt; flipping the mode in either direction changes its digest
and rejects before cached success or executor entry. Existing memory/disk
checks, V2 publication, legacy cleanup migration, no-clobber first publication,
directory barriers, leases, and tombstones are preserved. No new journal writer
or compatibility path is introduced.

Environment, working directory, and terminal fields remain data-only and their
effects remain explicitly refused. Their codec regression retains that boundary;
the prior foundation assertion that changing the override mode is unadmitted is
now superseded by the actual `intent-request-mismatch` oracle.

## Authored evidence

Fifteen new scenarios have authored manual mirrors: six helper cases, six
provider cases, and three CI request/builder cases. Full provider argv vectors
check literal values and build-mount order. Exact scripted creates verify
identical replay and both mode changes, using the real executor-entry counter.
Invalid executable cases reject before logical reservation or executor calls.
Existing foundation specifications retain their source coverage with the changed
mode/codec expectations.

All scenarios are **UNEXECUTED**. Podman is absent, and the available unchanged
producer's known `secure_memory.fill_span` failure reaches this SHA256 closure.
No runtime build or diagnostic was retried. SPipe/docgen, compiler/lib/MCP
checks, pinned-image execution, startup/latency/RSS measurements, and production
readiness remain unqualified. No runtime or generated-manual PASS is claimed.
