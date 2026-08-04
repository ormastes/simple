# NFR Requirements: Clang 23.1 Browser Demo Migration

- NFR-001 Reproducibility: Pin the current rc2 tag/commit and retain tool hashes; stable 23.1 substitution requires the same admission gates.
- NFR-002 Reliability: All missing, mixed-version, wrong-target, invalid-ELF, unstaged-payload, source-changed, and missing-capture states fail closed.
- NFR-003 Portability: Support configurable absolute toolchain prefixes and documented macOS ARM64, Linux x86_64/ARM64, and Windows x64/ARM64 discovery without assuming `clang-23` exists.
- NFR-004 Maintainability: Centralize 23.1 admission and avoid duplicated version parsing or independent fallback arrays in hot paths.
- NFR-005 Performance: Tool discovery performs bounded executable/version probes only; no recursive scans or downloads occur in compiler or request hot paths.
- NFR-006 Security: Official source/binary identity is retained and verified; build scripts never download or execute an unverified toolchain implicitly.
- NFR-007 Compatibility: Preserve the repository's x86_64, AArch64, RV32/RV64, WASM, freestanding, and section-GC expectations with focused compile/link tests.
- NFR-008 Evidence: Every final gate records exact tool paths, versions, hashes, commands, target triples, output identities, and artifact paths.
- NFR-009 Iteration safety: Each acceptance gate runs at most once on unchanged inputs and the lane stops after three fix/verify cycles.
