# SimpleOS image CLI V1 scenarios

Requirement: `REQ-016`. Executable source:
`test/01_unit/os/image_cli_v1_spec.spl`.

This manual describes the executable assertions. Runtime results remain
unqualified until an admitted self-hosted SSpec runner executes them.

## Project an explicit request

1. Supply the canonical x86_64 SimpleOS target and an intentionally absent root.
2. Supply all artifact paths, output path, sector count, profile, and identities.
3. Parse the request and compare every projected field with its supplied value.
4. Validate the same request through the composer's shared pure preflight.

Parsing succeeds without opening the absent root. The absent optional compiler
stays absent; no source commit, artifact, profile, or version is synthesized.

## Inspect without running

1. Add `--show-plan` to the complete request.
2. Require `inspect_only` and run the CLI handler against the absent root.
3. Check that the rendered plan disclaims artifact reads, output writes,
   provider admission, artifact admission, and qualification.

The expected handler status is zero for inspection only. It is not evidence of
composition or host-provider availability.

## Exercise syntax and admission boundaries

Split `--name value` options and `--name=value` options produce the same request.
The 27-argument maximum admits all 13 split value options plus `--show-plan`.
An optional compiler is accepted for `dev` and rejected for `runtime`.

Negative cases cover missing values, unknown and repeated options, excess
arguments, oversized paths, control characters, unsafe root/output paths,
source/output aliasing, another target, invalid profile or identities, invalid
decimal syntax, and sector counts outside 8–32768. Both sector boundaries pass
preflight; the real filesystem composer still decides whether materialization
at the requested capacity can succeed.

## Inspect help

`--help` and `-h` return zero without forming an image request. Empty input
returns nonzero. Help identifies the native provider requirement, canonical
manifest stdout format, and the distinction between composing an NVFS carrier
and qualifying firmware boot or release.

Real-byte composition, exclusive publication, descriptor lifetime, persisted
readback, and exact digests remain covered by the separate
[verified owner scenarios](installer/verified_image_composition_owner_v1_spec.md)
and native-provider checks. This CLI spec does not replace those gates.
