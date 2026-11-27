# Linux owned executable pin refused every image over 64 MiB (static-LLVM Stage 2 is 177 MB)

- Status: verification-pending (fix landed; needs a Stage 2 rebuild whose compiler-test rows run real HIR workers)
- Severity: P1. Phase 2 admits Stage 2, then `stage2-compiler-tests` rejects it: `compiler_cli_build` and `test_runner_build` fail with `HIR aggregate failure`.
- Found: 2026-11-20, during the ubuntu-p2 (WSL2, kernel 6.18) phase 2 bring-up at `3d6d4c16fce`
- Component: `src/runtime/runtime_process_owned.c` (Linux pin, acquire and digest)
- Related: `profile_hir_workers_linux_pin_rejects_dynamic_elf_2026-11-12.md` (the same symptom, an earlier cause)

## Observation
The phase 2 run was `bootstrap-from-scratch.sh --full-bootstrap --stop-after-stage2 --mode=dynload`, and its verdict was `ABORTED: stage=stage2-compiler-tests`:

```
[hir-shard] owner=0/3@0 status=CRASH exit=-1 claimed=0 sealed=0 finished=false
[hir-shard] owner=0/3@0 reason: owned executable pin was rejected
error: HIR aggregate failure; final worker and artifact publication blocked
```

The admitted Stage 2 compiler is 177,292,408 bytes. LLVM 23.1 is linked statically (vendored inkwell, `llvm23-1-force-static`). The ELF shape passed every loader-closure rule: one PT_INTERP pointing at the root-owned `/lib64/ld-linux-x86-64.so.2`, no RPATH or RUNPATH, and bare sonames only.

## Root cause
`rt_process_pin_executable` refused `st_size > 64 MiB` before it ever reached ELF admission. `rt_process_acquire_pinned_executable` and `rt_process_pinned_executable_sha256_value` carried the same literal cap. The pin printed no reason, so all the caller saw was the generic "owned executable pin was rejected".

## Fix
- The three caps are now one named bound, `RT_HAL_PIN_IMAGE_MAX_BYTES`, set to 1 GiB. Pin, acquire and digest must agree, otherwise acquire would refuse an image that pin admitted.
- A refusal now prints `[rt-pin] refused: <reason> (size, limit ...)` on stderr, mirroring the existing admission line.

## Tests
In `src/compiler_rust/runtime/src/value/sffi/env_process.rs`, module `linux_owned_pin_tests`:
- `owned_pin_admits_image_larger_than_64_mib` is the repro. It pins a 200 MiB padded dynamic ELF, then checks acquire and the digest. It failed before the fix and passes after it.
- `owned_pin_refuses_image_above_bound` covers the similar pattern: an image just over 1 GiB is still refused.
- Command: `cargo test -p simple-runtime --lib linux_owned_pin`. Result: 3 passed (WSL2 6.18, LLVM 23.1.1).

## Notes for reviewers
- Each pin copies the whole image into a sealed memfd, about 177 MB of tmpfs per pinned compiler. This is the same per-pin cost the 64 MiB images already paid, just larger.
- An alternative, not done here, is to shrink the image by linking LLVM dynamically. That needs a RUNPATH-free system libLLVM, which the pin's loader rules would admit.
