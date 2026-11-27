# Interpreter: slice/min/max interleaved with write_span re-decodes the whole array (2026-11-17)

Status: OPEN (seed interpreter; worked around in `emu_draw_shadow_rect`).

On the Rust seed (`/home/yoon/.cache/cargo-target-webrender-vk/release/simple`, 59635056 B),
a `[u32]` read method (`slice`, `min`, `max`) that follows a `write_span` on the SAME array
costs O(array), not O(span). The array was `mk(N).pixels`, a local `var` in a function.

Repro (scratch `span_probe2.spl`, N = 3,657,600, 200 rows of
`outp.slice(base+100, base+3300)`, `seg.min() == seg.max()`, then
`outp.write_span([7u32; 3200], base+100, 0, 3200)`):

| measure | result |
|---------|--------|
| `slice` per call | 13.7 ms (2.75 s / 200) |
| `write_span` per call | 9.9 ms (1.98 s / 200) |
| same `slice` x20 on an array that is never written | 0.02 ms each after the first (first call about 0.6 ms) |
| `write_span` x100 alone on a struct-field array | 8.5 us each |

Cost in the real caller: the first version of `emu_draw_shadow_rect` spent 10.2 s in `slice` and
6.4 s in `write_span` over 1016 rows. Reading from a never-written `src` and writing a separate
`outp` removed it (row loop 19.3 s -> 2.3 s).

Not isolated: an index store (`a[i] = v`) interleaved with reads; only `write_span` was measured.

Work-around cost: two region-sized arrays instead of one. A real fix belongs in the seed's array
method dispatch (do not re-decode the backing store on a read that follows an in-place write).
Context: `doc/08_tracking/bug/web_render_dpr4_residual_per_pixel_cost_2026-11-16.md`.
