# SimpleOS image and shell CLI projections

Requirement: `REQ-016`

## Image composition fails closed

Given the verified NVFS artifact producer and `SimpleOsImageManifestV1`
composer are not yet joined by a production CLI owner, `simple os image`
returns a non-zero status and explains which evidence boundary is missing. It
does not call the legacy installer builder, create a descriptor or placeholder
image, sign, publish, or write physical media.

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
