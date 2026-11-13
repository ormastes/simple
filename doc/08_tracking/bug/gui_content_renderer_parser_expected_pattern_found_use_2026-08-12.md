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

---

## Addendum 2026-11-11 — lane comp11 — SUPERSEDED confirmed on the tracked seed

Lane: `work/p3-comp11-20261111` on `origin/release/1.0.0` (base `41935a5f61860`).
Runtime: tracked seed `bin/simple.exe` build commit `46fe8f6b6def` (2026-11-10) —
one refresh earlier than the compiler2 addendum's 0791c2b7f4a7, so the pin was
re-run on this lane's own sanctioned binary.

Fresh seed-smoke (`SIMPLE_LIB=src SIMPLE_BINARY=$PWD/bin/simple.exe
bin/simple.exe test
test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_adv_spec.spl
--mode=interpreter --no-cache`, evidence
`build/review/comp11-probes/row8_drawir.log`): the spec **compiles and
executes 70 examples** (the doc recorded ZERO) — `declared>=70 executed=70
passed=69 failed=1`. The parser diagnostic
`Unexpected token: expected pattern, found Use` on
`src/lib/gc_async_mut/ui/gui_content_renderer.spl` is GONE; the module is
accepted. The parser-closure acceptance (reduce/repair/parity prerequisites in
the doc) is met in that the blocking parse failure no longer exists and the
DrawIR oracle runs.

The single failure is the SAME residual the compiler2 addendum flagged, not
the parser bug: `stages retained Vulkan composition damage for a partial host
refresh` — `expected 48 to equal 4` — a retained-Vulkan-damage staging count
on this host, while the sibling Vulkan tests in the same file pass ("keeps
retained Vulkan production frames device resident", "fails closed before
strict Vulkan primitive execution without a Vulkan engine"). That staging
count belongs in a separate row; this row's disposition stands SUPERSEDED.
No source change taken.

## Addendum 2026-11-13 — lane p3-comp1 (worktree p3comp1-wt, branch work/p3-compiler-p1-20261113)

Concurs with the recorded disposition: SUPERSEDED — the surviving failure is
a retained-Vulkan-damage staging count on the host, not the parser defect.
No in-lane change.

## Re-verified 2026-11-13 (Linux aarch64, lane uia)

On release/1.0.0 35144b7f5e9, Linux aarch64 seed af717f53d6bce3e5 after 69166cadc70 put a fn between the use lines of gui_content_renderer.spl: test/01_unit/lib/gc_async_mut/ui/gui_content_renderer_spec.spl parses and executes 3 examples with no expected-pattern-found-Use error; test/02_integration/rendering/host_gui_content_frame_spec.spl 1/1. The 2 assertion failures in gui_content_renderer_spec (retained seed returns false on cpu) are a different defect, filed separately.

