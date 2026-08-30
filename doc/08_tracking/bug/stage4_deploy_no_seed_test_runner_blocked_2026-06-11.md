# stage4 deploy left no seed driver — `bin/simple test` blocked host-wide

Date: 2026-06-11
Status: resolved (2026-06-12 — seed rebuilt; deploy-gate implemented in bootstrap-from-scratch.sh)
Owner: stage4 deploy lane

## Resolution (2026-06-12)

Rebuilt the seed with `cargo build --profile bootstrap -p simple-driver
-p simple-native-all` → `src/compiler_rust/target/bootstrap/simple`.
Two vendored-source fixes were required:

- `vendor/log/src/lib.rs`: the minimal log shim lacked the `log_enabled!`
  macro form needed by vendored regalloc2 v0.11.2 (it only had a function);
  added a no-op `log_enabled!` returning false.
- `vendor/log/.cargo-checksum.json`: updated the `src/lib.rs` sha256 so cargo
  accepts the modified vendored source.

Verified: `setsid timeout 30 bin/simple -c "print(1+1)"` → 2;
`bin/simple test` runs again via seed delegation (engine2d lane re-verified:
directx 18/18, order 4/4, cuda 7/7, rocm 7/7, acceleration 24/24, vulkan
processing 22/22, vulkan drawing 22/22). The suggested deploy-gate fix
(refuse to swap bin/simple without a working probed seed) is implemented:
`bootstrap-from-scratch.sh --deploy` now probes the `simple_seed` delegate
(installing it from a probed cargo build if absent), refuses the swap when no
working seed exists, and smoke-tests the deployed binary post-swap with
automatic restore of the previous binary on failure.

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
