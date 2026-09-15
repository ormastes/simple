# Seed-compiled fixtures die with SIGILL (public_dup / cfg_dup dispatch specs) (2026-09-15)

`bin/simple` is currently the Rust seed (`bin/release/aarch64-unknown-linux-gnu/simple`,
prints the bootstrap-seed banner). Two dispatch-contract specs drive the seed
binary directly at `src/compiler_rust/target/bootstrap/simple`:

- `public_dup_signature_dispatch_spec.spl` — compile+run of a tiny 3-module
  program (`pick(i64)` vs `pick(bool)` selective import) exits with
  `Illegal instruction (core dumped)` on BOTH examples.
- `cfg_dup_signature_dispatch_spec.spl` — the `@cfg` variant-dispatch fixture
  likewise dies `Illegal instruction (core dumped)` (2 failures).

Spec-side drift already fixed and kept: the seed path is now resolved absolute
(`rt_path_absolute`) because the spec shells out after `cd`-ing into a temp
dir, which used to break the relative path (`/bin/sh: ... not found`). The
crash is in the compiled artifact, not the invocation.

## Unblock condition

Real codegen regression in the seed (or in whatever `target/bootstrap/simple`
currently is). Reproduce: run the spec, read the `expected Illegal instruction
(core dumped) to contain PASS` lines. Fix the seed's compiled-output crash,
then re-run both specs.

## Related environment blocker

`main_opt_level_cli_spec.spl` shells `bin/release/simple` (a wrapper that
refuses to exec any binary identifying as a bootstrap seed). With the seed
currently deployed in the release slot the wrapper exits
`error: refusing non-production Simple runtime` before the driver runs — the
spec is blocked until a production self-hosted binary is redeployed. Not a
spec defect.
