# Native-build removed runtime bundle false-green

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 02).

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
