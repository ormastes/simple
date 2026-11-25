# Native-build removed runtime bundle false-green

## Verified closed 2026-11-25 (p2w3-af lane, release/1.0.0 @ 1457ddaa176)

Header was stale ("Open 2026-09-16 — needs owner triage" claiming "no
resolution evidence found in the body") — the body documents the fix and its
spec evidence, and the fix is present at HEAD. Code-inspection verification:

- `src/app/cli/bootstrap_main.spl:414-419` —
  `native_build_runtime_bundle_is_removed` covers all six removed aliases
  (`hosted`, `rust-hosted`, `rust_hosted`, `hosted-runtime`, `rust-runtime`,
  `all`).
- `run_native_build_bootstrap` checks the parsed args pre-FFI and fails
  closed: `bootstrap_main.spl:580` (`removed_bundle = ...`) → `:614-617`
  prints `Error: runtime bundle '<name>' was removed; use simple-core or
  core-c-bootstrap` and returns 1, before any `rt_native_build` delegation;
  `--help`/`-h`/`--list-optimizations` still short-circuit to exit 0 first,
  matching the documented help behavior.
- The full CLI predicate uses the same alias set
  (`src/app/io/_CliCompile/compile_targets.spl:2082`).
- All three named specs exist in-tree:
  `test/01_unit/app/cli/bootstrap_main_source_spec.spl`,
  `test/01_unit/app/compile/cli_compile_surface_spec.spl`,
  `test/02_integration/os/port/runtime_bundle_policy_spec.spl`.

Behavioral re-run is environment-blocked on this host: invoking the path via
`bin/simple.exe run src/app/cli/bootstrap_main.spl native-build
--runtime-bundle rust-hosted ...` fails during source load with
`unknown decorator '@representation_boundary'` (the known repo-wide
seed/source inconsistency at this HEAD), and the pinned binary is the Rust
seed, not the pure-Simple Stage-2 compiler this bug concerned. Verification
is therefore by code inspection only; the Stage-2/Stage-4 qualification
caveat in the body stands as written. Status: **closed** (fix landed and
present; header corrected).

## Open 2026-09-16 — needs owner triage (superseded; kept for history)

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

## Symptom

A fresh pure-Simple Stage 2 compiler accepted
`native-build --runtime-bundle rust-hosted --entry <file> -o <output>`.
The Rust bridge printed that the bundle was removed, created no output, but
returned exit 0.

## Root cause and fix

`bootstrap_main.run_native_build_bootstrap` delegated explicit-entry builds
directly to `rt_native_build`, bypassing the full pure-Simple CLI's correct
fail-closed return path. Bootstrap now rejects every removed hosted alias before
the FFI boundary: `hosted`, `rust-hosted`, `rust_hosted`, `hosted-runtime`,
`rust-runtime`, and `all`. The full CLI predicate uses the same alias set.

## Evidence

- Temporary source execution rejected `--runtime-bundle=all` with exit 1 and
  no output artifact; an earlier `--help` remained a successful informational
  request while a removed bundle before help still failed.
- `bootstrap_main_source_spec.spl` proves pre-FFI validation is present.
- `cli_compile_surface_spec.spl` requires the removed-bundle diagnostic for
  split, inline, and repeated forms across all six aliases.
- `runtime_bundle_policy_spec.spl` proves the Simple/C-only policy surface.

## Qualification blocker

The final synchronized incremental bootstrap closure reused the 675-object
cache and the supported `core-c-bootstrap` lane. It remained CPU-bound for 900
seconds, emitted no log output, and produced no artifact, so the bounded run was
terminated once. No retry was started.

Fresh deployed Stage-2/Stage-4 qualification remains pending. Before retrying,
instrument or bound entry-closure discovery so this silent CPU-bound phase
identifies its current module.

