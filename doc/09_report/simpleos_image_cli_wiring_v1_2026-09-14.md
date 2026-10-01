# SimpleOS image CLI wiring V1

Date: 2026-09-14. Scope: `REQ-016` image command projection through the existing
verified NVFS composition owner. Status: source/spec implementation; runtime
execution remains `MissingEvidence`.

## Change

`simple os image` now parses bounded explicit inputs and delegates execution to
`simpleos_verified_image_compose_v1`. The shared request preflight executes
before retained-root acquisition and is reused by pure `--show-plan` inspection.
It validates root/path shape, distinct paths, size bounds, profile/compiler
policy, and manifest identities. The CLI adds exact target and argument syntax
validation; no build identity or artifact location is inferred.

The Linux native retained-root provider remains the filesystem authority.
Unsupported providers fail closed. Success emits the existing canonical
manifest framing plus one stdout newline. The image is an NVFS carrier;
neither composition nor inspection asserts firmware boot, guest compiler
execution, persistence after reboot, signing, or release admission.

## Focused evidence

- Source inspection: no direct environment/process/pathname-I/O bypass,
  placeholder assertions, or permissive fallback in the new CLI module.
- Added six SSpec scenarios covering request projection, inspection, split
  options, bounded parsing, shared admission rejection, and usage.
- Updated the existing image/shell/bootstrap command contract and its manual;
  added a dedicated image CLI guide and manual.
- Attempted once:
  `timeout 60s bin/release/simple test test/01_unit/os/image_cli_v1_spec.spl --mode=interpreter`.
  The production wrapper exited 1 immediately with
  `refusing non-production Simple runtime: /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple`.
  The spec did not execute. No seed fallback, image creation, or runtime PASS
  is claimed.

## Remaining acceptance

An admitted self-hosted runtime must execute the focused CLI and verified-owner
specs, compile the CLI with the native provider, and create/read back a real
image with canonical manifest identity. The native provider's independent C
selfchecks and source review do not establish this compiled Simple path.
