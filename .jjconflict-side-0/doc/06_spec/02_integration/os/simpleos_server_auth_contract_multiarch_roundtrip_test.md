# SimpleOS server authentication multi-architecture roundtrip

Mirror of `test/02_integration/os/simpleos_server_auth_contract_multiarch_roundtrip_test.shs`.

The shell integration test builds trusted canonical-body tools for x86_64, ARM64, and RISC-V64, signs generated server media, recomputes each body with Simple, compares digests, verifies Ed25519 signatures, and rejects cross-architecture body/signature substitution.

This test is executable when the configured admitted compiler and admission file are available. If either prerequisite is unavailable it reports `SKIP`, so a passing invocation is meaningful only when the final `PASS` line is emitted.
