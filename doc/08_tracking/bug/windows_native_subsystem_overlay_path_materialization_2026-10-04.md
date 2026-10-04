# Windows native subsystem product overlay setup fails before tests

Status: OPEN pending native qualification. Diagnostic workaround and canonical filesystem repair tested; canonical builder/receipt integration is implemented in the isolated candidate. Canonical bug-database registration awaits the functioning self-hosted reconciliation owner; no database checksum is hand-edited.

Observed source: 9737d1217bc44439b56bba6c2ef16faaff51bd20. Diagnostic compiler: Cranelift-produced PE SHA256 776ce2a1b8b0f92d44e5dd70b5fac365ba96187f76cfa0ffc2c5bdcac8fdae40. Evidence: runtime/windows-restart-20261004/native-subsystem-products-post-link2/cranelift/artifact/matrix.json, terminal.json and owner/build.log under the shared Simple runtime store.

The overlay writer failed on a 261-character absolute path ending in the 92-character filename interp_optimizer_step_writes_lost_training_silently_produces_unchanged_weights_2026-08-18.md. Its parent directory existed. The three native products were NOT_RUN; registered and executed test counts were unavailable. This was setup failure, not three failing tests.

A distinct diagnostic generation native-subsystem-products-post-link2-overlayfix1/cranelift uses the short private root C:/snp/p2c-ov1 and extended absolute Windows I/O. It preserves the source archive selection, byte contents, alias targets, prior attempts and source/producer pins. Eight filesystem checks passed, including a path over 260 characters, identical bytes/hash, hardlink/junction creation, escape rejection and overwrite refusal. This is not canonical admission or a native product PASS.

Canonical owners still affected:
- scripts/bootstrap/build-compiler-subsystem-test-product.shs hardcodes job_root/source-overlay and a src-only sparse materialization.
- scripts/bootstrap/verify-compiler-subsystem-test-product.pl binds that fixed location and input manifest.

Repair must update both owner and verifier: a short separately owned overlay must retain canonical snapshot and link inventory authority, materialize required test/config/variant inputs and declared Windows aliases, reject arbitrary external/reparse/escaping paths, and preserve every changed-source/cache identity. Diagnostic source-materialization.json cannot substitute for source authority or BuildRunner task contexts.

Regression boundary: real Windows long-path materialization and source membership; missing/configuration/alias inputs rejected; six actual subsystem binaries compiler/interpreter/loader across LLVM/Cranelift each compile, enumerate registered cases, then execute with real pass/fail/skip totals. Full Windows qualification remains pending.

The canonical candidate allocates the entire long-prefix Windows generation beneath the same drive's short `.simple-product-jobs` namespace. The requested task output is a data reference, never a junction. Its generation record binds source HEAD, canonical source snapshot bytes, exact inventory and both existing producer/receipt identities. Resume rejects replacing or adding a producer. The selected callback mirrors only the already-verified result bytes and keeps its physical binary/evidence paths. Matrix verification resolves the same bound generation.

Builder and product verifier now share one selected-input catalog, including configuration, variants, tests and declared aliases. Alias targets are physically expanded with exact origin/hash rows; arbitrary links, missing targets, cycles, extra files and unhydrated LFS pointers are rejected. Expansion is capped at 200,000 members and 4,096 aliases. The canonical source snapshot remains authoritative. Existing generated-product manifest equality remains required; the materialization manifest cannot grant admission.

The exact frozen 9737 source read-only preflight found 65,776 selected tracked members, 13 aliases and zero LFS pointers among present selected files. Its aliases appear as modified/deleted/untracked entries in Git porcelain, so the source clean gate now admits only exact verified alias expansions while rejecting every other tracked/staged/untracked change.

Focused evidence: 18 filesystem checks passed; 8 additional boundary checks passed; a real Windows junction rejection passed after correcting the fixture's MSYS command argument conversion (only that failed fixture was rerun). Separate source-alias gate tests cover correct physical expansions and reject changed bytes, undeclared descendants, changed declaring source and staged mode changes. No native test product execution or qualification is claimed by these filesystem tests.
