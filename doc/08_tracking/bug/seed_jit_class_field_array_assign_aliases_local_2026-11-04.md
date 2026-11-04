# Seed JIT: assigning a local array to a class field aliases it (interpreter copies)

- **Filed:** 2026-11-04 (u8param lane)
- **Status:** OPEN — seed JIT value-semantics divergence; not fixed here.
- **Platform:** aarch64-apple-darwin, seed built from `release/1.0.0` (includes `bafc15f38a7`)

## Repro

```simple
class Hold:
    buf: [u32]
    me poke():
        self.buf[0] = 9u32
fn main():
    var a: [u32] = [1u32, 2u32]
    var h = Hold(buf: [])
    h.buf = a
    h.poke()
    print "a0={a[0]} h0={h.buf[0]}"
main()
```

| mode | output |
|---|---|
| `SIMPLE_EXECUTION_MODE=interpreter simple run` | `a0=1 h0=9` |
| `simple run` (JIT) | `a0=9 h0=9` |

Local-to-local `var b = a` copies in both modes (`a0=1 b0=9`), so only the
field-store path aliases.

## Impact

`backend_vulkan_font.spl` packed single-submit oracle: `oracle.buf = oracle_before`
then `oracle.draw_image_blend(...)` mutates `oracle_before` under JIT, so
`readback_nonblank_pixels` is 0 and Vulkan font promotion never succeeds under
`simple run` (see `macos_vulkan_2d_vector_font_empty_batch_native_fault_2026-07-26.md`,
2026-11-04 section).

## Fix direction

JIT lowering of a field store of an array value must give the field its own
copy-on-write handle (match the interpreter), rather than the Simple source
adding a defensive `.clone()`.
