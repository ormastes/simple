# Optimizer CLI Warning Flood Can Overrun Agent Context

Date: 2026-06-27
Status: resolved
Severity: medium

Resolution (2026-06-28): optimizer CLI now defaults to a concise per-pass count
report (stdout 2409 → 16 lines on the renderer repro); per-location detail is
opt-in via `--verbose` (src/app/optimize/analyze.spl + main.spl). The remaining
~940 stderr lines are compiler/lint diagnostics emitted from main.spl's import
graph (src/lib/**) before main() runs and are outside this CLI's control.

## Summary

`bin/simple run src/app/optimize/main.spl <file> --full --level=O3` can emit
thousands of unrelated compiler and lint warnings before the actionable
optimization summary. In an agent session this creates avoidable context growth
and increases crash/runaway risk.

## Reproduction

Run the optimizer on a touched renderer or spec file, for example:

```sh
timeout 120s bin/simple run src/app/optimize/main.spl \
  src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl \
  --full --level=O3
```

## Expected

The optimizer should default to a concise report for the target file, or provide
a documented quiet mode that suppresses unrelated compiler/lint warnings while
keeping failures visible.

## Actual

The command succeeds but prints a large warning stream from unrelated compiler
modules before the target-file optimization summary.

## Impact

SPipe optimization lanes require this command on touched `.spl` files. The
current output volume wastes context and can contribute to Codex session crashes
or runaway behavior.
