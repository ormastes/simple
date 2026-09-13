# SimpleOS image, shell, and bootstrap CLI projections

Requirement: `REQ-016`

## Image composition requires explicit verified inputs

`simple os image` projects explicit artifact paths, a new output path, sector
count, profile, and identities into the verified composition owner. Missing
inputs return nonzero. Help exposes the native retained-root requirement and
canonical `SimpleOsImageManifestV1` stdout encoding. Native Linux mechanisms
now exist; unsupported hosts and filesystem mechanisms fail closed.

The dedicated [image CLI scenarios](image_cli_v1_spec.md) cover bounded parsing
and inert inspection. These are source/spec contracts, not evidence that a
deployed self-hosted runtime has executed the composer successfully.

## Shell inspection reuses the QEMU plan owner

`simple os shell --show-plan` and `simple os shell --print-command` delegate to
the existing sealed inspection owner. Interactive launch fails closed because
the established runner captures output and cannot attach host stdin. A future
interactive session must use a `ProcessLaunchSpecV1`-capable provider rather
than adding another QEMU policy owner.

## Help is capability-honest

The OS help describes image composition as a verified NVFS carrier and points
to its explicit input options. It continues to mark interactive shell launch
unavailable. Composition does not claim firmware boot or release qualification.

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
