# Lint profile split argument is rejected

Status: Fixed in source; pure-Simple redeploy verification pending

The deployed `bin/simple lint <file> --profile robust` command compiles the
lint tool but then exits 2 with `--profile requires a tier`. The option parser
does not consume the following token consistently. This prevents the robust
SFFI lint profile from serving as a reliable command-line release gate even
though the focused `raw_sffi_call_spec.spl` checks pass.

The CLI now canonicalizes the split spelling to `--profile=robust` before
calling the lint engine, rejects a missing/option-shaped tier, and has a
contract check for a successful split-form invocation. Redeploy the pure-Simple
binary before closing this record against the production launcher.

Source-driven launcher checks now reach a terminal JSON verdict with the split
form for both the HTTP server and thread-pool SFFI modules. The prerequisite
missing `source_may_contain_dangerous_keyword` lint helper was restored with an
allocation-free conservative registry scan and its focused admission spec
passes.
