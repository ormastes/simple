# Windows native subsystem product overlay setup fails before tests

Status: OPEN. Diagnostic workaround verified; canonical builder/receipt integration pending. Canonical bug-database registration awaits the functioning self-hosted reconciliation owner; no database checksum is hand-edited.

Observed source: 9737d1217bc44439b56bba6c2ef16faaff51bd20. Diagnostic compiler: Cranelift-produced PE SHA256 776ce2a1b8b0f92d44e5dd70b5fac365ba96187f76cfa0ffc2c5bdcac8fdae40. Evidence: runtime/windows-restart-20261004/native-subsystem-products-post-link2/cranelift/artifact/matrix.json, terminal.json and owner/build.log under the shared Simple runtime store.

The overlay writer failed on a 261-character absolute path ending in the 92-character filename interp_optimizer_step_writes_lost_training_silently_produces_unchanged_weights_2026-08-18.md. Its parent directory existed. The three native products were NOT_RUN; registered and executed test counts were unavailable. This was setup failure, not three failing tests.

A distinct diagnostic generation native-subsystem-products-post-link2-overlayfix1/cranelift uses the short private root C:/snp/p2c-ov1 and extended absolute Windows I/O. It preserves the source archive selection, byte contents, alias targets, prior attempts and source/producer pins. Eight filesystem checks passed, including a path over 260 characters, identical bytes/hash, hardlink/junction creation, escape rejection and overwrite refusal. This is not canonical admission or a native product PASS.

Canonical owners still affected:
- scripts/bootstrap/build-compiler-subsystem-test-product.shs hardcodes job_root/source-overlay and a src-only sparse materialization.
- scripts/bootstrap/verify-compiler-subsystem-test-product.pl binds that fixed location and input manifest.

Repair must update both owner and verifier: a short separately owned overlay must retain canonical snapshot and link inventory authority, materialize required test/config/variant inputs and declared Windows aliases, reject arbitrary external/reparse/escaping paths, and preserve every changed-source/cache identity. Diagnostic source-materialization.json cannot substitute for source authority or BuildRunner task contexts.

Regression boundary: real Windows long-path materialization and source membership; missing/configuration/alias inputs rejected; six actual subsystem binaries compiler/interpreter/loader across LLVM/Cranelift each compile, enumerate registered cases, then execute with real pass/fail/skip totals. Full Windows qualification remains pending.
