# Lint profile split argument is rejected

Status: Open

The deployed `bin/simple lint <file> --profile robust` command compiles the
lint tool but then exits 2 with `--profile requires a tier`. The option parser
does not consume the following token consistently. This prevents the robust
SFFI lint profile from serving as a reliable command-line release gate even
though the focused `raw_sffi_call_spec.spl` checks pass.

Required fix: accept the documented split argument and `--profile=robust`
forms consistently, reject unknown tiers, and add CLI integration coverage for
the resulting exit status and SFFI009/SFFI010 diagnostics.
