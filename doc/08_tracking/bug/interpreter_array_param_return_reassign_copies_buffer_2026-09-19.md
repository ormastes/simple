# `b = helper(b, x)` copies the whole array on every call (seed interpreter)

- Found: 2026-09-19, lane C4 (internal ELF linker performance)
- Binary: `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple`,
  51,607,912 bytes, mtime 2026-09-19 09:09:30, sha256 `350328bab5142ff4…`,
  `Simple Language v1.0.0-beta.12` (Rust bootstrap seed, interpreter path —
  the module under test was dropped to the interpreter by
  `[jit-fallback] unresolved external symbol`)
- Host: aarch64, 20 CPUs, shared box
- Status: OPEN — not fixed, worked around in the ELF linker (see below)

## What happens

The idiomatic accumulator shape in this repo

```simple
var b: [i64] = []
b = write_u64_le(b, value)      # helper appends and returns the buffer
```

copies the ENTIRE buffer on every call, because the argument and the caller's
variable both reference it, so the helper's `var r = buf` takes a copy. Writing
the same appends inline (`b = b.push(x)`) does not copy. Measured with the
binary above, one process, three sizes:

| appends | inline `b = b.push(x)` | `b = helper(b, x)` | `b = helper8(b, x)` (8 bytes/call) |
|---|---|---|---|
| 5,000 | 0.19 ms | 223 ms | 33 ms |
| 20,000 | 0.70 ms | 2.81 s | 414 ms |
| 80,000 | 3.27 ms | 102.06 s | 9.79 s |

Inline appends are linear; the helper form is quadratic — 31,000x slower at
80k appends. Batching more bytes per call divides the constant by the batch
size but stays quadratic.

Related, same session, same binary:

```simple
fn mutate(b: [i64]) -> [i64]:
    var r = b
    r[0] = 9
    r
```

`mutate([1,2,3])` returns `[9,2,3]` and leaves the caller's array `[1,2,3]` —
i.e. `var r = b` is a copy, not an alias. An in-place patch helper is therefore
still O(n) per call; only writes to a buffer that the current function owns are
O(1).

Repro (the fixtures used above are in the lane's scratch dir, and are five
lines each): declare an unresolvable `extern fn` in the script so the module
drops to the interpreter, then time `b = b.push(x)` against
`b = push_one(b, x)` for n = 5,000 / 20,000 / 80,000.

## Why it matters

This is not a micro-optimization detail: it silently makes every byte-buffer
builder in the tree quadratic in output size. In the internal ELF linker it was
the second-largest cost after relocation patching — `elf_write_image`,
`elf_append_symtab`, `elf_build_symtab` and the GOT/`.rela` builders all used
the helper shape, so a 698 KB image was copied tens of thousands of times.

## The workaround now in the tree (and what it costs)

`doc/10_metrics/compiler/linker/internal_elf_engine_perf_2026-09-19.md` fix 2:
the ELF writer paths now append inline and call the per-record encoders on an
EMPTY buffer (`for x in write_u64_le([], v): b = b.push(x)`), which keeps one
definition of each encoding while never handing a big buffer across a call
boundary. That is a workaround for this defect, not a design preference — it is
recorded here rather than normalized silently, per CLAUDE.md.

Cost of the workaround: every hot buffer builder in the linker is now written
in a shape chosen for the interpreter's copy behaviour, and anyone editing
those functions must keep appends inline or the quadratic cost returns with no
test failing (outputs stay byte-identical; only time changes).

## What a real fix would look like

Any one of:

1. Move-on-last-use (or refcount-1 in-place mutation) for array parameters, so
   `b = helper(b, x)` with no other live reference mutates in place.
2. A bulk `extend` / `append_slice` / `slice` provider for `[u8]`/`[i64]` in
   `std`, so a buffer append is one runtime call regardless of length. There is
   currently no such primitive — every "bulk" copy in the linker is an
   interpreted per-element loop.
3. A mutable-reference parameter mode (`inout`-style) for byte buffers.

Until one of those exists, the inline-append rule above is load-bearing for
linker performance.
