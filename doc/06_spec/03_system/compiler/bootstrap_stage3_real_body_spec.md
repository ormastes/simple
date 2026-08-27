# Stage3 Real Entry Body Regression

This executable system specification proves that an explicitly selected,
admitted pure-Simple Stage3 compiler can build and execute a nontrivial entry
body. It also binds the compiler banner to the canonical semantic version in
`release/version.sdn`; `VERSION` and `bootstrap_identity.spl` are checked
projections of that authority.

The scenario:

1. Requires `SIMPLE_STAGE3_BIN` to name an existing non-seed compiler.
2. Checks `--version` against the canonical release version.
3. Writes a helper-calling Simple program whose marker requires real execution.
4. Builds it with Stage3 and stub fallback disabled.
5. Executes the artifact and requires the exact marker and exit status.

Executable source:
`test/03_system/compiler/bootstrap_stage3_real_body_spec.spl`.
