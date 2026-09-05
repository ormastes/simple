# native-build --entry-closure collects zero source files for an existing entry (blocks CUDA/Vulkan parity probe)

- **Date:** 2026-08-19
- **Status:** OPEN
- **Severity:** medium — blocks `check-processing-cuda-fill-native.shs` and `check-processing-cuda-vulkan-native-parity.shs` (probe-binary-missing)

## Repro
The documented recipe
(`doc/06_spec/03_system/app/simpleos_gpu_host/processing_cuda_fill_native_contract_spec.md`):

```sh
cd /mnt/data/worktrees/render-harden
bin/simple native-build \
  --source src/compiler --source src/app --source src/lib \
  --entry-closure --entry src/app/test/processing_cuda_fill_probe.spl \
  --strip --output build/simpleos_gpu_host/cuda_fill_native/processing_cuda_fill_probe
```

fails with:

```
error: native-build entry 'src/app/test/processing_cuda_fill_probe.spl' collected zero source files:
--entry takes a path to a .spl file ... resolved relative to the current working directory
```

The file EXISTS at that path (verified with `ls`), and an absolute `--entry`
path fails identically, so the error message's diagnosis (bad path / module
path) is wrong — entry-closure collection itself returns an empty set. Binary:
`bin/release/x86_64-unknown-linux-gnu/simple` (Rust seed, 2026-08-18 deploy).

## Impact
The parity probe binary can no longer be produced, so the "cuda offload with
vulkan" parity lane reports `processing_cuda_fill_native_status=blocked
reason=probe-binary-missing`. CUDA itself is healthy on this host:
`check-cuda-generated-2d-readback.shs` PASSes (64 device pixels, 0 mismatch)
and `check-cuda-dlopen-fallback.shs` PASSes.

## Next step
Debug the entry-closure collector in the native-build path (seed CLI) or
regenerate the probe with a stage binary once bootstrap redeploy is unblocked.
