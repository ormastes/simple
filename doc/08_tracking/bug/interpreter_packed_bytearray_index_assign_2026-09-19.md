# `buf[i] = v` is refused on a packed `[u8]` in the seed interpreter (2026-09-19)

Status: OPEN. Found by lane C5 while making the internal ELF link engine
assemble its buffers as packed bytes.

## Symptom

Index assignment into a packed byte array fails at runtime:

```
error: semantic: invalid assignment: cannot index assign value of type array
```

Minimal repro (seed interpreter; the module must be interpreted, so the
script calls something the JIT drops — importing and calling `elf_link` is
enough, see "Reproducing" below):

```simple
val raw = file_read_bytes("some.bin")   # -> Value::ByteArray (packed)
var buf = raw[0:1024]                   # slice of a packed array stays packed
buf[3] = 0                              # <-- refused
```

The same statement succeeds when `buf` is an ordinary `Value::Array`.

## Why it is a defect and not a language rule

The interpreter has TWO index-assignment paths and they disagree:

- `src/compiler_rust/compiler/src/interpreter/place.rs:213` DOES support it —
  `Arc::make_mut(bytes)[idx] = byte`, copy-on-write, in place.
- `src/compiler_rust/compiler/src/interpreter/node_exec.rs:1409,1422` — the
  path a plain `name[i] = v` statement takes — has arms for `Value::Array`,
  `Value::Dict`, `Value::Tuple` and `__setitem__` objects, and falls through
  to the error above for `Value::ByteArray`. `type_name()` reports `array`,
  which is why the message reads as if an array were being refused.

So the capability exists, is already implemented with the right semantics,
and is simply not reachable from the statement form. Reading (`buf[i]`) and
slicing (`buf[a:b]`) of a packed array both work.

## Cost being paid for the workaround

The ELF engine now assembles every buffer packed (a packed concat is a
runtime memcpy; an interpreted `push` per byte is ~880 ns each) but has to
widen each finished buffer back to `[i64]` with `empty_arr.concat(packed)`
before anything can patch it. That widening happens in four places:

- `elf_static_contents` (`elf/elf_static_link.spl`) — one per output section,
  because the relocation patch loop writes `buf[r.out_off + wi] = ...`
- `elf_append_symtab` (same file) — before its `elf_put_le` patches
- `elf_build_symtab` (same file)
- `elf_write_image` (`elf/elf_exec_writer.spl`) — callers index-assign the image

Each widening allocates one boxed `Value` per byte, which is the whole reason
the engine's live set is ~24x the size of the image it is building. With this
fixed, every one of those buffers stays packed end to end, the four
`.concat()` calls disappear, and the engine's own memory drops by roughly the
same factor.

A second, smaller consequence: `Value::byte_array_values` widens to
`Value::UInt { width: 8 }`, so a widened buffer holds 8-bit values, and
`x << 8` on one of them wraps to 0. Lane C5 had to add `as i64` in
`elf_rd_le`, `read_u32_le` and `read_i64_le` for that reason; the sha256 gate
caught it (1,003 bytes of a synth-20 link came out zeroed). If packed buffers
stop being widened, that hazard goes away with them.

## Reproducing

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
    var buf = text_to_bytes("hello")
    buf[0] = 72
    print "ok {buf[0]}"
    0
SPL
bin/simple run /tmp/repro.spl
```

## Suggested fix

Add a `Value::ByteArray` arm to the `node_exec.rs` index-assignment match that
does what `place.rs:213` already does: reject a value outside `0..=255` with a
clear message, otherwise `Arc::make_mut(bytes)[idx] = byte`. A frozen byte
array must keep failing, as the other frozen mutations do.
