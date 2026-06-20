# IDE Plugin Architecture NFR Requirements

## Selection

Selected NFR option: **Option 2, VS Code-Style Host Targets**. Full dynamic install/uninstall is deferred until external plugins need live runtime updates.

## Requirements

- NFR-IPA-001: Built-in plugin manifest cache load SHOULD stay under 25 ms warm.
- NFR-IPA-002: First activation for built-in plugins SHOULD stay under 50 ms warm.
- NFR-IPA-003: Hot command dispatch overhead SHOULD stay under 2 ms p95, excluding plugin work.
- NFR-IPA-004: Registry invalidation event propagation SHOULD stay under 100 ms.
- NFR-IPA-005: No plugin may mutate UI, document, or workspace state without an explicit capability token.
- NFR-IPA-006: Feature-check paths MUST remain pure: no host GUI, browser, network, shell-out, or desktop API dependency.
- NFR-IPA-007: Runtime plugin install/uninstall, DI rebinding for external plugins, and live aspect reordering are out of scope for the first Office suite milestone.

## Verification

| Requirement | Evidence |
| --- | --- |
| NFR-IPA-001 | Covered by `test/01_unit/app/ide/ide_plugin_architecture_nfr_spec.spl`. |
| NFR-IPA-002 | Covered by `test/01_unit/app/ide/ide_plugin_architecture_nfr_spec.spl`. |
| NFR-IPA-003 | Covered by `test/01_unit/app/ide/ide_plugin_architecture_nfr_spec.spl`. |
| NFR-IPA-004 | Covered by `test/01_unit/app/ide/ide_plugin_architecture_nfr_spec.spl`. |
| NFR-IPA-005 | Covered structurally by `OfficePluginContext` checks and `ide_office_plugin_suite_spec.spl` context-mismatch assertions. |
| NFR-IPA-006 | Covered by `bin/simple-interp src/app/ide/main.spl --feature-check --tui` and `--gui` pure feature checks. |
| NFR-IPA-007 | Covered by `doc/04_architecture/ide_plugin_architecture.md` migration step 7. |
