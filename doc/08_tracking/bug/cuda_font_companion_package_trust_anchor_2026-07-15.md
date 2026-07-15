# CUDA font companion lacks a production package trust anchor

Date: 2026-07-15

## Impact

The pure-Simple portable emitter and checker can generate and authenticate a
CUDA font PTX for retained test evidence, and Engine2D can validate and install
caller-supplied bytes. Production construction cannot safely auto-install that
artifact because the only generated copy is mutable ignored `build/` output.

## Evidence

- `scripts/check/check-portable-compute-toolchains.shs` writes PTX and its
  self-reported SHA-256 under `build/portable_compute_toolchains`.
- `Engine2D.install_cuda_font_artifact` checks payload/hash consistency,
  program version, bounds, and the versioned entry before session mutation.
- `PackageVerify` explicitly skips checksum verification and assumes success.
- `package/build.spl` still returns `checksum_placeholder`.

The artifact and its adjacent evidence share one mutable producer; neither
supplies an independent production trust decision. The embedded Vulkan font
artifact is the closest valid pattern, but a CUDA equivalent needs a retained,
Simple-generated PTX and pinned digest before it can be tracked honestly.

## Completion criteria

1. A package manifest or generated tracked module binds the PTX bytes to an
   immutable expected SHA-256 and `FONT_ATLAS_COMPOSITE_PROGRAM_VERSION`.
2. The trust owner computes and compares the real digest before exposing bytes
   to Engine2D; mismatch and missing metadata fail closed.
3. The package/bootstrap owner passes authenticated bytes to the canonical
   Engine2D CUDA construction path without environment reads or `build/` path
   discovery inside the library.
4. Static tamper tests and retained CUDA device-origin readback prove the
   packaged path. CPU replay remains authoritative when the companion is absent
   under Suggested/Preferred policy; Required policy fails closed.

Do not solve this by embedding handwritten PTX, trusting an adjacent evidence
file, or adding a second font renderer, cache, or kernel.

## Fresh-session resume

After deploying a current pure-Simple self-hosted binary, run this once from the
repository root on the NVIDIA host:

```sh
CUDA_ARCH=compute_75 SIMPLE_BIN=bin/simple \
  sh scripts/check/check-portable-compute-toolchains.shs
```

Accept the generation input only when `evidence.env` reports
`cuda_font_status=compiled_artifact_verified`, the exact versioned font symbol,
and current Simple invocation/runtime plus emitter/source/artifact SHA-256 rows.
The adjacent hash remains test provenance; independently pin the accepted PTX
in its package manifest or tracked generated module before factory installation.
