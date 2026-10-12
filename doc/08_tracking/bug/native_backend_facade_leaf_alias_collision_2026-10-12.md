# Nested backend leaf incorrectly aliased to a facade

Status: source repaired; executable regressions NOT_RUN.

The admitted Stage 2 producer
`4c479a0d3f25bcb73a9c4c8fe1735b7743c65862076c73e079b7f7bc9c607036`
passed the prior nested-loader boundary and failed full CLI source closure with
a physical-owner collision. Both `src/compiler/70.backend/__init__.spl` and
`src/compiler/70.backend/backend/mir_test_builder_full.spl` were labelled
`compiler.backend.mir_test_builder_full`. Evidence is line 51 of
`/mnt/wsl/simple-dbc-native-bootstrap-20261012/stage2-compiler-tests/x86_64-unknown-linux-gnu/verification/logs/compiler_cli_build.log`,
snapshot `scv-revision-v1-4ff6e6c6c84192e9ca4c9576ff4e65b6281512c5a572719c3dfc62e1ddebb8c8`.

The ordered-root resolver missed the nested backend leaf, stripped the terminal
segment, and aliased its package facade to the leaf spelling. This is the same
missing compatibility-owner probe class as the loader failure. Renaming or
coalescing distinct physical sources would hide the resolver defect.

The repair factors the loader probe into a private helper limited to declared
same-name nested compiler families: blocks, mir_opt, backend, and loader. It
probes within each selected root only after direct resolution fails, before
parent stripping, and preserves exact physical-owner and collision guards.
It excludes explicit nested spellings and arbitrary library/package families.
Both compiler-root and broad src-root forms preserve ambiguity propagation.

Authored regressions cover the actual failing backend leaf under both root
forms, existing blocks/mir_opt nested leaves, and the explicit backend nested
spelling. Existing loader overlay and ambiguity scenarios remain in the same
precedence spec. These runtime scenarios remain NOT_RUN until a qualified runner
is available. The frozen native source and live compiler matrix were untouched.
