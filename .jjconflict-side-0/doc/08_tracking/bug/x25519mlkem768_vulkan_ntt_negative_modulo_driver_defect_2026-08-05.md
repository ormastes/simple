# X25519MLKEM768 Vulkan NTT coefficient mismatch — root-caused: negative-operand `%` on the NVIDIA Vulkan compute path

Date: 2026-08-05
Worktree: `/home/ormastes/dev/pub/simple/.claude/worktrees/x25519-paired-timing`
Relates to: `x25519mlkem768_vulkan_spirv_artifact_missing_2026-08-05.md` (same
campaign, AC-5 Vulkan lane)
Historical predecessor (not present in this worktree, only in
`/home/ormastes/dev/pub/simple/build/worktrees/simpleos-engine2d-stage4-snapshot/doc/08_tracking/bug/`):
`x25519mlkem768_vulkan_ntt_barrier_mismatch_2026-08-02.md`

## Status

Root cause identified with fresh, this-host evidence. The specific pinned
artifact (see the artifact-missing doc above) now passes cleanly, 28/28,
across a full stage-by-stage, both-direction, both-device sweep. One
discrepancy with the historical record is flagged, unresolved, at the end of
this doc — read that section before assuming this fully closes the
historical bug's timeline.

## Background: why the old bug doc isn't reachable from this worktree

T-02 (Vulkan session-layer restoration) reported that the historical
barrier-mismatch bug doc "doesn't even exist here" and could not be
reproduced or refuted. That's correct: it was never committed anywhere, and
lives only as an untracked (`??`) file in a different worktree
(`build/worktrees/simpleos-engine2d-stage4-snapshot/`). This session found
that worktree only *after* independently reproducing the same failure
signature from scratch (see "Independent reproduction" below) — the
convergence between the two is itself evidence, not something assumed.

## Independent reproduction (before the historical doc was found)

Starting from the CPU oracle in
`test/fixtures/crypto/x25519mlkem768/vulkan_ntt_probe.c` (`scalar_ntt`/
`scalar_intt`, zetas table, modulus 3329, fixture
`(poly*97 + i*29 + 17) % 3329`), this session wrote its own from-scratch GLSL
forward/inverse NTT compute shader (not copied from anywhere), naive
reduction: `int r = value % Q; if (r < 0) { r += Q; }`. Compiled with
`glslangValidator --target-env vulkan1.1`, `spirv-val` clean, and run through
the existing `vulkan_ntt_probe.c` against both physical devices
(`NVIDIA TITAN RTX`, `NVIDIA RTX A6000`):

```
$ ./vulkan_ntt_probe ntt_forward.spv forward 1
device=0 mismatch index=128 expected=849 actual=2202
device=1 mismatch index=128 expected=849 actual=2202

$ ./vulkan_ntt_probe ntt_forward.spv forward 7
device=0 mismatch index=2 expected=1970 actual=3323
device=1 mismatch index=2 expected=1970 actual=3323
```

Both numbers (`index=128, expected=849, actual=2202` at stage 1; and
`index=2, expected=1970, actual=3323` at stage 7) are the **exact** figures
recorded in the historical bug doc's 2026-08-02 reproduction and 2026-08-03
native rerun, independently reproduced by a differently-authored shader on
the same two physical devices. That is strong evidence this is a genuine,
deterministic, host/driver-level defect — not an artifact of one particular
shader's authorship.

## Isolating the cause

A pure-CPU Python simulation of this session's exact per-thread indexing
formula (block/offset/zeta-index derivation) against the same scalar oracle,
for every partial stage count 1 through 7, produced **zero** mismatches —
proving the algorithm/indexing math itself is correct and the divergence is
introduced by the GPU execution, not the shader's arithmetic design.

A minimal shader with **no shared memory, no barriers, no ping-pong** —
direct SSBO reads and a single butterfly write per invocation — reproduced
the identical `index=128, expected=849, actual=2202` mismatch at stage 1.
This rules out shared-memory races/barrier ordering entirely: the trivial
shader has neither.

Coefficients 0–127 (the "lower = reduce(a+b)" write, whose operand to `%` is
never negative) matched every time. Coefficients 128–255 (the
"upper = reduce(a−b)" write, whose operand is negative roughly half the
time) were the only ones that ever mismatched. Testing reduction variants on
the trivial shader:

| variant | formula | stage-1 result |
|---|---|---|
| naive branch | `r = value % Q; if (r<0) r += Q;` | **FAIL** (849 → 2202) |
| double-mod | `r = ((value % Q) + Q) % Q;` | **FAIL** (849 → 2202) |
| force-positive bias | `r = (value + Q*1000000) % Q;` | **PASS** |

The double-mod idiom still fails because it still evaluates `value % Q` with
a negative `value` as its *first* step — the already-wrong result then
propagates through the rest of the expression. Only avoiding a negative
operand to `%` **entirely** fixes it. Conclusion: this NVIDIA Vulkan compute
driver stack (`driver_version=2434761728`, `api_version=4211000`, i.e. Vulkan
1.3.275 loader / `libnvidia-gl-580` ICD) mis-evaluates GLSL's `%` (which
lowers to SPIR-V `OpSMod`) for a negative dividend, at least under this
toolchain (`glslangValidator` 15.1.0). A safe, overflow-free general fix used
for the rest of this session's verification: `(value + Q) % Q`, valid for any
`value` in `[-Q, ...)` — the NTT butterfly difference is always in
`[-(Q-1), Q-1]`, so a single `+Q` bias is always sufficient and never
overflows a 32-bit `int`.

## The original (pinned-hash) shader already had a targeted defense — and its comment names this exact bug

`src/os/crypto/x25519_mlkem768/kernels/ml_kem_ntt_forward.comp` (restored
from the snapshot worktree; reproduces the pinned SPIR-V hash bit-for-bit —
see the artifact-missing doc) already contains:

```glsl
int modq(int value) {
    if (value < 0) {
        // Never feed a negative operand to SPIR-V remainder. NVIDIA's Vulkan
        // path has reduced -2480 as uint32, yielding 2202 instead of 849.
        // -(value + 1) is defined even for INT_MIN; add the removed unit only
        // after the positive remainder has bounded the magnitude.
        int magnitude = -(value + 1);
        int residue = ((magnitude % 3329) + 1) % 3329;
        return residue == 0 ? 0 : 3329 - residue;
    }
    return value % 3329;
}
```

This confirms the original authors had already independently diagnosed the
identical defect (their comment literally names the `2202` symptom) and
wrote a magnitude-based guard for it that also never passes a negative
operand to `%`. Verified algebraically and empirically on this host: for
`value = -2480`, `magnitude = 2479`, `residue = (2479+1) % 3329 = 2480`,
return `3329 - 2480 = 849` — correct. Compiling just this `modq` inside a
trivial no-shared-memory shader on this host: **PASS**, stage 1, both
devices.

## Fresh, this-host result: the pinned original now passes completely

Compiling the **unmodified** original `.comp` sources (both forward's
`modq`-guarded/ping-pong version above and the analogous inverse shader)
with `glslangValidator --target-env vulkan1.1` reproduces the pinned SHA-256
hashes bit-for-bit
(`0865f588f0825a3ff66a1d5e2cd2a9d0c356bb75b4fceaaf5c2196ffa05f6379` forward,
`07a11b541ef204a4fb6c907338dafc99bdf870d2046edcfad02a3d42dcca2687` inverse),
and the official check script
(`scripts/check/check-x25519mlkem768-vulkan-ntt.shs`, copied in from the
snapshot worktree) sweeps stage counts 1 through 7, both directions, both
physical devices — **28/28 PASS**, `oracle_match=1` on every line. Full
transcript and the exact command are in the companion artifact-missing doc.

## Unresolved discrepancy — flagged, not explained away

The historical bug doc's last entry (2026-08-03 "native rerun and revised
localization") reports that a native run — of what its surrounding text
describes as the post-repair, ping-pong + `modq`-guarded version — **still**
failed with the identical `index=128, expected=849, actual=2202` signature.
Today, compiling and running what is represented as that same, unmodified
source passes cleanly, 28/28. Two honest possibilities, neither confirmed:

1. The driver/toolchain state on this host changed between 2026-08-03 and
   today (2026-08-05) in a way that happens to fix this specific `OpSMod`
   defect — plausible (NVIDIA driver or Mesa loader updates land often) but
   not verified here (no historical driver-version log was found to diff
   against `driver_version=2434761728`).
2. The exact `.comp` content the 2026-08-03 rerun actually executed was not
   preserved to disk in a way this session can distinguish from the current
   file by content alone (the bug doc's next section after that failing run
   is a further, undated "prepared repair" description with no confirming
   rerun logged afterward) — i.e. the file on disk today may postdate that
   failing run.

This session did not have access to whatever build artifact the 2026-08-03
run actually consumed, so it cannot adjudicate between these. What **is**
independently, freshly verified on this host today: the current
`.comp` sources compile to the exact pinned hashes and execute correctly,
oracle-matched, on both physical devices, across every stage count.

## Acceptance condition (unchanged from the historical doc, now met)

"Both physical NVIDIA devices must report compile, submit, fence completion,
device-origin readback, and all-coefficient oracle equality." — met, 2026-08-05,
this worktree, `NVIDIA TITAN RTX` and `NVIDIA RTX A6000`, stages 1–7,
forward and inverse.

## Files referenced

- `src/os/crypto/x25519_mlkem768/kernels/ml_kem_ntt_forward.comp`,
  `ml_kem_ntt_inverse.comp` (restored into this worktree, not committed)
- `test/fixtures/crypto/x25519mlkem768/vulkan_ntt_probe.c` (pre-existing in
  this worktree, unmodified)
- `scripts/check/check-x25519mlkem768-vulkan-ntt.shs` (restored into this
  worktree, not committed)
- `build/evidence/x25519mlkem768/vulkan/x25519mlkem768_ntt_forward.spv`,
  `..._inverse.spv` (freshly built, gitignored, not committed)
