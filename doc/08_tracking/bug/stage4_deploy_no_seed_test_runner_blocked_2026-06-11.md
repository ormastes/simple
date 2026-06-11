# stage4 deploy left no seed driver — `bin/simple test` blocked host-wide

Date: 2026-06-11
Status: open
Owner: stage4 deploy lane

## Summary

After the stage4 self-hosted deploy (~2026-06-11 15:32, "stage4 DEPLOYED with
seed delegation"), `bin/simple` points at
`bin/release/x86_64-unknown-linux-gnu/simple` (self-hosted). Running
`bin/simple test <spec>` now fails fast with:

```
error: cannot run tests: the test runner would re-spawn this same binary (bin/simple).
  Provide a Rust seed driver via SIMPLE_BOOTSTRAP_DRIVER or keep
  src/compiler_rust/target/{bootstrap,release}/simple available.
```

The self-exec fork-bomb guard works as designed, but neither seed path
exists on this host (`src/compiler_rust/target/` has no built binaries), so
the documented remedy is not satisfiable without a full cargo build.

## Fallback attempted

`SIMPLE_BOOTSTRAP_DRIVER=bin/release/simple.bak.pre_new` runs, but that
binary fails to parse current source ("parse error: Unexpected token:
expected identifier, found Gpu") — consistent with the known self-hosted
lean-parser language-coverage gaps that had the deploy gate at matrix 6/8.

## Impact

All interpreter-mode spec verification on this host is blocked until either
the Rust seed is rebuilt (`cd src/compiler_rust && cargo build --release`)
or the deploy is rolled back to the seed binary. GPU-lane specs verified
green earlier today (backend_directx 18/18, order 4/4, acceleration 24/24,
vulkan processing/drawing, cuda/rocm processing 7/7+7/7) all ran BEFORE the
swap.

## Suggested fix

Deploy script should refuse to switch `bin/simple` to the self-hosted binary
unless a working seed driver exists at one of the two documented paths (probe
by actually running `<seed> --version`), keeping the delegation contract it
advertises.
