# Stage 3 backend segfault after HIR in GPU dynload bootstrap

## Status

Open. This blocks admission of a full CLI compiler and physical Vulkan Engine2D readback verification.

## Reproduction

On Linux x86_64, build and admit Stage 2 with `bootstrap-from-scratch.sh` in
`dynload` mode, mint a `//bootstrap:stage3` planner admission, then resume Stage
3 with the mandated single job/thread.

## Evidence

- Final source revision: `ce34a9c47e`
- Admitted Stage 2 SHA-256: `647fda08ed424a1275f90bd94f2902de1cfdb4e48954b5aca5d9fcc0f17cdd0d`
- Stage 3 reached memory snapshot sequence 1391, phase `hir-complete`.
- The last snapshot recorded 1,112,268,313 live heap bytes and 2,718,968 KiB RSS.
- The process remained CPU-bound in backend generation, then exited with
  `Segmentation fault (core dumped)`.
- Kernel evidence: `simple` faulted at address `0x1261f2018`, instruction offset
  `0x6fe568`, error 4.
- No Stage 3 candidate, sanity receipt, or provenance manifest was produced.

The preceding attempt ended during HIR under unrelated host-wide OOM pressure;
this isolated final attempt passed that frontier and failed independently after
HIR, so this is not classified as the same OOM failure.

## Required follow-up

Symbolize offset `0x6fe568` against the admitted Stage 2 binary, reproduce with
backend crash diagnostics enabled, and repair the pure-Simple compiler before
retrying bootstrap. Do not substitute the Rust seed or admit the Stage 2 binary
as a full CLI compiler.
