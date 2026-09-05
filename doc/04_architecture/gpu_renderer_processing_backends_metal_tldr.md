# Metal MSL Processing Backend — TLDR

Validated shared `ProcessingIr` deterministically generates a fail-closed
`ProcessingBackendArtifact`; the existing Metal SFFI alone owns native resource
lifecycle and produces device-origin evidence.  Semantic/ABI/version keys drive
cache invalidation.  Linux proves source and failure contracts only; macOS must
compile, submit, read back, and match the CPU oracle.
