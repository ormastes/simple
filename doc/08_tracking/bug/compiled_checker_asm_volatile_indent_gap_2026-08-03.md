# Compiled checker asm-volatile indented-block gap

- Status: **open, rerouted** — still open, but **the reproduction recipe below
  is stale and will not reproduce as written.** Corrected 2026-09-02 against
  `origin/main` @ `1b76db1d6c3`.

  `src/lib/nogc_async_mut_noalloc/baremetal/riscv/cmo.spl` — the file this
  record tells you to run the rebuilt checker against — **no longer contains an
  `asm volatile:` block at all.** It now routes every cache-maintenance op
  through extern runtime providers (`extern fn rt_riscv64_prefetch_w`,
  `rt_riscv64_prefetch_i`, `rt_riscv64_fence_i`, each behind an
  `@unsafe(reason: ..., capabilities: [ffi])` attribute and an
  `unsafe(capabilities: [ffi]):` block). `/usr/bin/grep -c asm <that file>`
  returns 1, and it is not an asm block. Line 57 is now an `extern fn`
  declaration, not the canonical indented asm form.

  The grammar gap itself is NOT closed — the construct is still live elsewhere:
  `/usr/bin/grep -rn "asm volatile:" src/lib/` finds it in
  `src/lib/nogc_async_mut_noalloc/baremetal/riscv32/startup.spl` at `:111`,
  `:165`, `:265`, `:301`, and `:311` (the last as the single-line
  `asm volatile: "wfi"` form, which is a second shape worth covering). **Retarget
  the reproduction to `riscv32/startup.spl`.**

  Left open, not fixed: confirming the defect requires the *rebuilt compiled
  checker*, i.e. a bootstrap cycle, which was out of scope for this pass (one was
  in flight). Reason: **needs-bootstrap**.

- Status (historical): open, rerouted
- Severity: P1 (Stage 4 inventory blocker)
- Found by: `stage4_expr_batch`
- Owner: inline-assembly primary parser (unclaimed)

After the expression batch fixed the `unsafe:` diagnostic in frozen row
`source-000201`, the rebuilt compiled checker progressed to line 57 of
`src/lib/nogc_async_mut_noalloc/baremetal/riscv/cmo.spl` and reported
`expected string literal in asm block` for the canonical `asm volatile:`
indented form. This is a later independent grammar root; it is not evidence
that the unsafe-block fix failed.

Reproduce with the rebuilt checker against that exact file. The follow-up must
compare the Rust parser's `asm volatile:` grammar, preserve existing braced and
parenthesized asm behavior, and add exact, adjacent, malformed, and recovery
coverage before changing the asm owner.
