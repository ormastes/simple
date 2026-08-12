# GUI content renderer parser recovery failure — 2026-08-12

Status: OPEN.

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
