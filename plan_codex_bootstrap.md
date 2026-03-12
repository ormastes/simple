# Codex Bootstrap Plan

Updated: 2026-03-12

## Goal

Keep the bootstrap story in this checkout aligned with the code that actually exists, with Linux as the first fully verified host.

## Canonical Linux Flow

```bash
src/compiler_rust/target/bootstrap/simple --version
bin/release/simple build bootstrap
sha256sum bootstrap/simple_stage2 bootstrap/simple_stage3
```

Expected result:

- `bootstrap/simple_stage1` exists
- `bootstrap/simple_stage2` exists
- `bootstrap/simple_stage3` exists
- Stage 2 and Stage 3 hashes match

## Verified Status

Verified on Linux x86_64 on 2026-03-12:

- `bin/release/simple build bootstrap` completed successfully
- `bootstrap/simple_stage2` and `bootstrap/simple_stage3` were both produced
- `sha256` matched for Stage 2 and Stage 3

Hash observed during verification:

- `d4b0efbbea4e62c3d79603005e23d6bf1157b13a6d50b3f11df0c42e8fe19524`

## Remaining Work

### Linux

- keep README and build docs pointed at the working `simple build bootstrap` path
- avoid references to missing `scripts/bootstrap/*` wrappers unless they are restored

### FreeBSD

- restore or replace the missing QEMU/bootstrap wrapper entrypoint
- re-run the staged bootstrap on the guest and capture artifacts

### macOS and Windows

- restore or replace platform wrapper entrypoints
- validate the same Stage 1 -> Stage 2 -> Stage 3 contract on each host

## Notes

- `doc/build/bootstrap_multi_platform.md` is the matrix/status view
- `doc/build/bootstrap_pipeline.md` is historical and still contains references to wrapper scripts that are not present in this checkout
