# Pinned Phase 2 cannot initialize DevHub module static arrays by concatenation

- Canonical ID: `phase2_module_static_array_concat_initialization_2026_10_27`
- Status: open; source compatibility does not close the underlying bug.
- Owner: DevHub / compiler-runtime owners.
- Created: 2026-10-27.
- Producer: P2 `13d73267e690b2cdd46438315e2bfe6d4d6c0c37bcfc15591a921fc9728b270b`.
- Source: `src/app/devhub/gh_compat.spl`.
- Regression: `test/01_unit/app/devhub/gh_compat_spec.spl`.

The compatibility flag catalogs retain literal typed arrays instead of executing array concatenation while initializing module statics. Their public values remain unchanged. This is narrower than ordinary function-local array concatenation, which remains supported by other focused checks.

## Evidence

The retained literal tables were part of the earlier DevHub P2 source repair. Current GH JSON and flag native graphs compile and run successfully, but this is not a new independent replay of the original static-initializer failure. Related older registry issue native_array_concat_dispatch_bootstrap_2026_10_16 remains separate.

## Removal condition

Retire only after actual module-static concatenation preserves every flag value and method/type metadata under the deployed producer, with native command flag regressions and no startup evaluation error.

Commit identity and final receipts must be appended through the canonical BugDatabase API after integration. No compiler rebuild, standard SSpec execution or unexecuted matrix is claimed.
