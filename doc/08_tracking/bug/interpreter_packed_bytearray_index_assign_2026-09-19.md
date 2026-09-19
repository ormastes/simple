# Packed `[u8]` buffers cannot be used as build buffers in the seed interpreter (2026-09-19)

Status: OPEN. Two related seed-interpreter gaps, found by lane C5 while trying
to make the internal ELF link engine assemble its buffers as packed bytes. The
attempt worked and produced byte-identical output, and was **reverted** because
gap (b) broke 12 linker specs. Together they are what stands between the engine
and a measured ~2.5x on `elf_link` plus roughly a 24x cut in its live bytes.

Evidence and measurements:
`doc/10_metrics/compiler/linker/internal_elf_engine_memory_and_algorithms_2026-09-19.md`.

## Why this matters

In the seed interpreter, `Value::ByteArray(Arc<Vec<u8>>)` stores one byte per
element and its bulk operations are runtime memcpys, while a generic
`Value::Array` stores one boxed `Value` per element and is appended one
interpreted `push` at a time. Measured on 100 KB, with the module genuinely
interpreted:

| operation | per element |
|---|---|
| packed slice `raw[0:100000]` | **0.64 ns** |
| packed concat `sl + sl` | **~0.1 ns** |
| `Array` slice / `Array + Array` | 108 ns / 81 ns |
| interpreted push into `[i64]` | **880 ns** |

So a packed buffer is ~1,000x cheaper per byte to build and ~24x smaller. Every
image-building function in the ELF linker wants to be packed. Neither gap below
is a design decision — one is an unreachable code path, the other an
unconsidered consequence of a variant choice.

## Gap (a): `buf[i] = v` is refused on a packed `[u8]`

```
error: semantic: invalid assignment: cannot index assign value of type array
```

The interpreter has TWO index-assignment paths and they disagree:

- `src/compiler_rust/compiler/src/interpreter/place.rs:213` DOES support it —
  `Arc::make_mut(bytes)[idx] = byte`, copy-on-write, in place.
- `src/compiler_rust/compiler/src/interpreter/node_exec.rs:1409,1422` — the
  path a plain `name[i] = v` statement takes — has arms for `Value::Array`,
  `Value::Dict`, `Value::Tuple` and `__setitem__` objects, and falls through to
  the error above for `Value::ByteArray`. `type_name()` reports `array`, which
  is why the message reads as if an array were being refused.

Reading (`buf[i]`) and slicing (`buf[a:b]`) of a packed array both work. The
capability exists with the right semantics and is simply not reachable from the
statement form.

Consequence for the linker: the relocation patch loop and the ELF header
patches write `buf[i] = v`, so a packed buffer had to be widened back to a
generic array before anything could patch it — which is what led straight into
gap (b).

### Suggested fix

Add a `Value::ByteArray` arm to the `node_exec.rs` index-assignment match doing
what `place.rs:213` already does: reject a value outside `0..=255` with a clear
message, otherwise `Arc::make_mut(bytes)[idx] = byte`. A frozen byte array must
keep failing, as the other frozen mutations do.

## Gap (b): widening a packed array yields 8-bit values, and there is no bulk widening

`Value::byte_array_values` (`src/compiler_rust/compiler/src/value.rs:1991`)
widens packed bytes to `Value::UInt { value, width: 8 }`, not `Value::Int`.
`Value::UInt` "carries width so arithmetic ops can apply modulo-2^width wrap",
so on a widened buffer:

```simple
val hi = b[o + 1] << 8      # wraps to 0 — b[o+1] is 8 bits wide
val ok = (b[o + 1] as i64) << 8
```

Every route from packed to generic goes through that function —
`empty_array.concat(packed)`, `packed + array`, `array + packed`, slicing, any
array method on a packed receiver — so **there is no way to obtain an array of
`Int` elements from a packed buffer in bulk**. `.map(x => x as i64)` is
per-element interpreted (~880 ns each), i.e. exactly the cost the packed path
existed to avoid.

Consequence for the linker: `elf_link` declares `Result<[i64], text>`. The
packed version satisfied that structurally and produced byte-identical files,
but every consumer that reassembles a multi-byte field with
`(b[o + 1] & 0xff) << 8` silently read a truncated value. That is what the
specs' own `rd16`/`rd32`/`rd64` helpers do, and 12 linker spec files went red.
Notably the **sha256 output gate did not catch this** — the written bytes were
identical; only running the specs did.

(A different, earlier symptom of the same variant choice DID reach the output:
`elf_rd_le` truncated the existing instruction word before the AArch64
instruction-field merge, and 1,003 bytes of a synth-20 link came out zeroed.
The engine's own readers now widen with `as i64`, which is a good change on its
own merits and was kept.)

### Suggested fix

Either widen to `Value::Int` at that boundary (bytes are values, not `u8`
arithmetic, once they leave a packed array), or add an explicit bulk conversion
— e.g. a packed-array method that returns a generic array of `Int` in one pass
— so a function declared to return `[i64]` can assemble packed internally.

## Reproducing

Both need the module to be genuinely interpreted. A script that only imports
`elf_link` keeps its JIT module and runs natively, which hides the cost and
changes the timings by ~100x; calling `elf_link` drops the module.

```bash
cat > /tmp/repro.spl <<'SPL'
use compiler.backend.linker.elf.elf_static_link.{elf_link, ElfLinkRequest, ELF_LINK_STATIC_EXEC}
use compiler.backend.linker.reloc_engine.{RelocArch}
use std.string_core.{text_to_bytes}
fn main() -> i64:
    val objs: [[u8]] = []
    # forces the whole module to the interpreter (unresolved `elf_link` in the JIT)
    val _ = elf_link(ElfLinkRequest(objects: objs, archives: [], shared: [], entry: "_start",
        target: RelocArch.AArch64, mode: ELF_LINK_STATIC_EXEC, interp: ""))
    var packed = text_to_bytes("hello")

    # gap (b): widening yields 8-bit values
    val widened: [i64] = [].concat(packed)
    print "shift_wraps={widened[1] << 8}  correct={(widened[1] as i64) << 8}"

    # gap (a): index assignment into the packed array is refused
    packed[0] = 72
    print "never reached: {packed[0]}"
    0
SPL
bin/simple run /tmp/repro.spl
```
