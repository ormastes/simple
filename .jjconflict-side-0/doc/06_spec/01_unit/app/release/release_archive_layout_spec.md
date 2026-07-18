# Release Archive Layout Specification

> **Manual draft — pending canonical `spipe-docgen`.** This mirrors the
> executable unit SSpec while the pure-Simple runner is unavailable.

Executable source:
`test/01_unit/app/release/release_archive_layout_spec.spl`

## Find installer runtimes below the archive root

Linux and Windows installer preparation derives the extracted package root
from the selected `.spk` filename. Runtime lookup then uses that root instead
of incorrectly assuming that `bin/` was extracted at the artifact directory.

## Reuse the bootstrap launcher in the full fallback

The full-package job requires the successful Linux bootstrap job, downloads its
artifact, and copies its checked runtime and asset-root launcher into the full
archive. A missing runtime or launcher stops packaging instead of publishing a
falsely runnable archive. The artifact upload includes the fallback's `dist/`
output and checksum paths.
