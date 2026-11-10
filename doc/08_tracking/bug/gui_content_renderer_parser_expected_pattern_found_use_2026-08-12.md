# GUI content renderer parser recovery failure — 2026-08-12

Status: SUPERSEDED.

The retained GUI renderer currently prevents the Engine2D DrawIR parity spec
from compiling:

```text
parse: src/lib/gc_async_mut/ui/gui_content_renderer.spl:
Unexpected token: expected pattern, found Use
```

The diagnostic has no line/column and points at a later `use` token rather than
the originating construct. Three bounded repair/verify cycles normalized the
two new multiline imports and removed a trailing final function-parameter
comma, but the identical diagnostic remained. Prefix-only parser probes through
the import block pass, while the full module check exceeds the default
60-second CPU guard without returning a syntax location.

Impact: `composition_damage_spec` passes 6/6, `damage_plan_spec` passes 13/13,
and the WM retained idle spec passes 6/6, but
`draw_ir_adv_spec` executes zero examples. LOCAL retained replay therefore
cannot be promoted into WM/GUI until the parser reports and accepts the full
GUI module and the DrawIR pixel-parity oracle runs.

Required closure:

- Reduce the smallest failing suffix of `gui_content_renderer.spl` with a
  parser-only entrypoint that does not invoke the full compiler driver.
- Make the parser report the originating span for an unterminated pattern.
- Run the DrawIR retained LOCAL/full/idle pixel-parity spec after repair.

---

## Addendum 2026-11-11 — lane compiler2 — verdict SUPERSEDED (repro no longer reproduces)

Triage-first pass, batch 2. The parser-recovery failure blocking the DrawIR
spec is resolved on the refreshed seed (bin/simple.exe, build-commit
0791c2b7f4a7).

**Repro / pin spec:** `test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_adv_spec.spl`
— the exact spec this doc said "executes zero examples." Seed-smoke
(`test ... --mode=interpreter --no-cache`, refreshed seed): the spec now
**compiles and executes 70 examples** (was 0). The diagnostic
`Unexpected token: expected pattern, found Use` on
`gui_content_renderer.spl` is GONE — the module is accepted by the parser.

**Why it changed:** `src/lib/gc_async_mut/ui/gui_content_renderer.spl` was
rewritten since 2026-08-12 (current head has well-formed multiline imports at
lines 8-14 and a different `GuiRetainedRenderSession` structure — the
triggering construct is gone), and the seed parser received numerous
recovery/diagnostic fixes in the interval (e.g. `7a9c110c192b`,
`fc75b0d22aa7`, `fe10123e18fc`, among others). No single fixing commit was
isolated for this row; the operative evidence is that the repro no longer
reproduces. Evidence log: `build/review/p3c2-drawir-seedsmoke.log`.

**Residual (separate from this row):** the same spec file now shows **1 of 70**
failures — `stages retained Vulkan composition damage for a partial host
refresh`, `expected 48 to equal 4` — while sibling Vulkan tests in the same file
pass ("keeps retained Vulkan production frames device resident", "fails closed
before strict Vulkan primitive execution without a Vulkan engine"). This is a
retained-Vulkan-damage staging count on this host, NOT the parser bug, and was
not introduced by this lane (no source changes made). Flagged for a separate
row; do not conflate with the parser-closure acceptance, which is met.

**Cycles:** 0 (no live defect; no fix attempted).
