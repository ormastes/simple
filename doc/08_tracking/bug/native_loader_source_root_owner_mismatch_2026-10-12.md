# Nested loader owner rejected by source-root handoff

Status: source repaired; runtime regression NOT_RUN pending qualified runner.

The admitted Stage 2 compiler `041e685fdbb0bb24eeec571a28d8bea57537909cd642116372bf4a8407fce1c8`
failed full CLI entry-closure loading with `SOURCE_ROOT_OWNER_MISMATCH`.
The ordered-root resolver selected `src/compiler/99.loader/__init__.spl`, while
the loaded owner was `src/compiler/99.loader/loader/exec_mapping.spl`.
Retained evidence is the native bootstrap compiler matrix log:
`/mnt/wsl/simple-dbc-native-bootstrap-20261012/stage2-compiler-tests/x86_64-unknown-linux-gnu/verification/logs/compiler_cli_build.log`.
Its admitted snapshot revision was
`scv-revision-v1-54abfef0d9782235d5c7c3fece5fe2278e11aefc07f64bff2dca3f77c543f6a3`.

`compiler.loader.exec_mapping` is a compatibility spelling for a nested loader
leaf. Relative imports already loaded that leaf. The explicit-root resolver
looked for the leaf directly under the numbered loader root, then stripped the
terminal segment and found the package facade. The strict handoff check correctly
refused these distinct physical owners.

The source repair probes the nested loader spelling within each ordered root
after its direct spelling fails and before parent stripping. Direct overlay
owners remain preferred. Ambiguous numbered directories remain errors. Relative
imports, configured library families, and the exact physical-owner guard remain
unchanged. The package-only `compiler.loader` spelling keeps its facade.

Authored regression scenarios cover the real nested leaf through both `src/compiler`
and broad `src` source roots, terminal function
suffix, package facade, and an explicit overlay overriding the nested default.
They are NOT_RUN: the general test runner is not yet qualified. `git diff --check`
passed for the changed resolver and regression spec. The live frozen native
source and active matrix were not modified.

Existing ambiguity fixtures contain competing compiler driver and plugin owners,
not nested loader directories. The existing precedence spec exercises their
fail-closed ambiguity behavior through the same checked numbered-directory
helper used by both new nested probes. No new nested-loader ambiguity fixture
was added; direct runtime proof of that specific shape remains unavailable.
