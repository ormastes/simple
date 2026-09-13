# SimpleOS image, shell, and bootstrap CLI projections

Requirement: `REQ-016`

## Image composition remains fail-closed at the native CLI adapter

The verified composition owner now defines the complete retained-root,
persisted-readback, exact-output, and manifest flow. However, its safe hosted
read/write ABI is currently implemented only by the interpreter provider. The
production native runtime has no corresponding hooks. `simple os image`
therefore returns non-zero and names that exact provider gap instead of using
the interpreter, legacy descriptor builder, or an unsafe path-based fallback.

## Shell inspection reuses the QEMU plan owner

`simple os shell --show-plan` and `simple os shell --print-command` delegate to
the existing sealed inspection owner. Interactive launch fails closed because
the established runner captures output and cannot attach host stdin. A future
interactive session must use a `ProcessLaunchSpecV1`-capable provider rather
than adding another QEMU policy owner.

## Help is capability-honest

The OS help marks both actual interactive shell launch and image composition
unavailable while exposing their safe inspection/diagnostic surfaces. No
source-only projection is advertised as a working producer.

## Bootstrap inspection is receipt-oriented

`simple os bootstrap` fails closed unless `--show-plan` is present. The plan
first inspects the current sealed QEMU run lane and then describes the required
`EnvironmentSnapshotV1`, `SimpleOsImageManifestV1`, and release-evidence
admissions. It does not build, boot, download, sign, or publish anything.

The three guest operations are bounded `ProcessLaunchSpecV1` values:

1. `simple --version`
2. `simple build hello.spl -o hello`
3. `./hello`

Inspection always ends with `Qualified: false`; only the eventual evidence
producer may report qualification after a cold boot and receipt commit.
The inspected run lane is not release-firmware evidence; the plan names that
receipt as a separate prerequisite rather than upgrading preview evidence.
