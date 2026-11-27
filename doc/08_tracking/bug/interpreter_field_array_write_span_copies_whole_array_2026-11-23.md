# Interpreter: `self.field.write_span(...)` copies the whole field array per call (2026-11-23)

Status: OPEN (seed interpreter; worked around in `engine2d/backend_software.spl`).

Seed `/home/yoon/.cache/cargo-target-webrender-blend/release/simple`, `SIMPLE_EXECUTION_MODE=interpreter`.
A class with `buf: [u32]` of 3600 x 3040 (10.9M) elements, 100 calls each:

| form | cost per call |
|------|---------------|
| `self.buf.write_span(row, off, 0, 3600)` | 1.86 ms |
| `var b = self.buf; b.write_span(...); self.buf = b` (one write) | 1.77 ms |
| `var b = self.buf; self.buf = []; b.write_span(...); self.buf = b` | 3.9 us |
| `self.buf[i] = v` | 1.2 us |

Cause: the place write-back for a `write_span` receiver
(`interpreter_method/mod.rs`, `if method == "write_span"`) does
`arr.as_ref().clone()` of the receiver before the copy kernel, and a local that
still shares the field's array pays the same copy-on-write. Only a uniquely
owned array is written in place.

Real cost: every `SoftwareBackend` span primitive wrote through the field, so at
device scale 4 each span (even 1 px) cost one surface copy: a 20 x 20 rounded box
200 ms, a 3408 x 50020 section's fill 20 s (css-layout 4x).

Work-around: `SoftwareBackend.sw_buf_write_span` takes the field (leaves it
empty for the one write) and restores it; `sw_fill_rect_rows` and `draw_image`
take it once per call. Real fix: write the span in place into the place's array
when the receiver is a field/index place (no clone), as an index store already does.

