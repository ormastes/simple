# AC-4 SIMD byte-identity probe crashes on reproduction — reported PASS does not hold

**Status:** OPEN, UNSTABLE — do not treat as fixed. A dispatched root-cause
agent (session-limit-terminated before delivering a report) apparently left
"both probes healthy" as its last status line, and independent re-testing
now gets 6/6 consecutive PASS on `mlkem_ntt_simd_public_interface_probe.spl`
against the currently-deployed binary. **No source diff explains this** —
every file under `src/runtime/` and `src/compiler_rust/` was diffed against
origin and none contains an alignment-related change; the two files that ARE
modified in this area (`runtime_simd_dispatch.c/.h`) diff to unrelated
OpenCL-probe removals from a different concurrent session's work, not a
`rt_simd_mul_i32x8` fix. The most likely explanation is heap-layout-dependent
nondeterminism (consistent with the original 3x-SIGABRT-then-1x-SIGSEGV
pattern across different binary builds) rather than a genuine fix — the
underlying misalignment condition should be assumed to still exist until a
source-level root cause is found and landed. Re-run the reproduce steps
below under load / after other allocations to check whether it still
recurs before relying on this probe's green status for anything.
**Found:** 2026-08-05
**Severity:** HIGH — a landed campaign claim ("AC-4 x86 lane closed under
`interpret`, `ac4_x86_simd_public_interface_verdict=PASS ... checks_failed=0`")
does not survive independent reproduction; the probe crashes instead.
**Component:** `rt_simd_mul_i32x8` (`src/runtime/src/value/simd_int_ops.rs:705`),
exercised via `test/09_baselines/crypto/x25519mlkem768/mlkem_ntt_simd_public_interface_probe.spl`
**Attribution:** measured on the Rust bootstrap seed (`bin/simple` prints the
seed banner); no self-hosted binary exists in this worktree.

## What was claimed

A prior agent this session reported, for `mlkem_ntt_simd_public_interface_probe.spl`
run under `--engine interpret`:

> Verdict: `ac4_x86_simd_public_interface_verdict=PASS ... checks_failed=0`
> ... backend identity confirmed via `mlkem_ntt_simd_receipt().chunk_hits`
> (240/240 SIMD arms, 0/0 forced-scalar) and an independent gdb breakpoint
> instrument (1440 executions of `_mm256_mullo_epi32` in the SIMD arm, 0 in
> forced-scalar).

## What independent reproduction found

Running the **exact same probe file** (md5 `929b93568bcf76d20a76295f129a1b83`,
unchanged) with `SIMPLE_TIMEOUT_SECONDS=0 bin/simple run
test/09_baselines/crypto/x25519mlkem768/mlkem_ntt_simd_public_interface_probe.spl
--engine interpret` does not produce a verdict line. It crashes, every time:

- **3/3 runs** against a stale ad-hoc scratch seed build
  (`/tmp/.../scratchpad/simple-fixed`, a leftover debug build from an
  earlier point in this session — see the `bin/simple` symlink note below):
  identical `PANIC misaligned pointer dereference: address must be a
  multiple of 0x4 but is 0x...013d1` at `runtime/src/value/simd_int_ops.rs:705:13`,
  `thread caused non-unwinding panic. aborting.`, exit 134 (SIGABRT). The low
  address bits (`...013d1`) were identical across all 3 runs despite ASLR
  varying the high bits — a structural misalignment, not a random fluke.
- **1/1 run** against the correct, canonical binary
  (`bin/simple` → `bin/release/x86_64-unknown-linux-gnu/simple`, restored
  after finding the symlink had been pointing at the stale scratch build —
  see `doc/08_tracking/bug/bin_simple_symlink_pointed_at_stale_scratch_build_2026-08-05.md`):
  `Segmentation fault`, exit 139 (SIGSEGV). Different signal, same call site
  family (native SIMD intrinsic dereferencing a marshalled pointer), still a
  crash, not a verdict line.

So the crash is **not** an artifact of the wrong/stale binary — it reproduces
on the correct one too, just with a different fault (SIGSEGV vs SIGABRT,
plausibly because the two binaries were built with different
optimization/debug profiles that change heap layout around the same
underlying misalignment bug). md5 of the probe file was identical
before/after every run; not contamination.

## What this means for AC-4

The claimed PASS for the x86 SIMD lane through the public interface **does
not hold**. This bug doc supersedes that claim until the crash is fixed and
the probe is re-run and independently reproduced green. The forced-scalar
control probe (`mlkem_ntt_forced_scalar_control_probe.spl`) does run
successfully (`ac4_scalar_control_verdict=RAN forward_len=768 inverse_len=768`)
— only the SIMD arm crashes, which is at least consistent with a genuine
SIMD-path defect rather than a fixture problem.

## Not yet root-caused

This doc records the discrepancy and reproduction evidence; it does not
diagnose why `rt_simd_mul_i32x8` receives a misaligned pointer here when
earlier, narrower SIMD evidence in this campaign (the standalone AVX2
constant-multiplication probes referenced elsewhere in this session) did
not hit this fault. Next step: read `simd_int_ops.rs` around line 705 and
trace the allocation path for the array this probe constructs, under
`--engine interpret`, to find where the returned pointer loses its required
4-byte alignment.

## Reproduce

```
md5sum test/09_baselines/crypto/x25519mlkem768/mlkem_ntt_simd_public_interface_probe.spl
SIMPLE_TIMEOUT_SECONDS=0 bin/simple run \
  test/09_baselines/crypto/x25519mlkem768/mlkem_ntt_simd_public_interface_probe.spl \
  --engine interpret
echo "exit=$?"   # expect 139 (SIGSEGV) or 134 (SIGABRT), not a verdict line
```
