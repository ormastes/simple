# Missing suppression descriptions remain advisory under robust profiles

At release baseline `2f7439a9cebafe4fd34bd9743720e01faed2da5b`, `@allow(print_in_test_spec)` records a precise missing-description issue but `Linter.lint_source` hardcodes Warn for `LINTALLOW001` even after resolving Robust/Critical. Its absence from the configurable rule map correctly prevents self-suppression, but also means no profile projection corrects that hardcoded level.

Source repair: resolve only this admission diagnostic through the existing profile and warning-phase policy. Ordinary profiles remain Warn, explicit Robust/Critical return Deny, and the existing warning-phase migration lowers Deny to Warn. Preserve the nonconfigurable diagnostic, original warning, location and reason guidance; do not synthesize unsafe or suppression intent.

Seven positive fixture source strings are corrected first to explain their intentional suppressed condition. Their existing API assertions are retained. New actual-public-API SSpec controls exercise the precise failing profile boundary and its refusals. These are source-predicted regressions, not observed test failures: all ten new scenarios and affected retained contracts are UNRUN.

Open: qualified execution, complete warning census and root-cause cleanup, broader robust warning publication, CLI autofix use and performance qualification. This repair makes no whole-feature or warning-clean claim.
