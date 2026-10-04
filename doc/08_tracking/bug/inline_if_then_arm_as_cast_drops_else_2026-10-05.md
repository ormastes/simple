# Inline `if c: X as T else: Y` loses the else arm (2026-10-05)

**Status:** open (compiler). Linker call sites worked around by parenthesizing
the cast arm; the grammar/lowering defect itself is unfixed.

## Symptom

An inline if-expression whose THEN arm ends in an `as` cast is miscompiled:

```simple
fn g1(c: bool, x: i64) -> i64:
    val v = if c: x as i64 else: 7
    v
fn g2(c: bool, a: [u8]) -> i64:
    val v = if c: a[1] as i64 else: 7
    v
```

Measured with the x86_64 seed (`/root/work/host-seed-target/bootstrap/simple run`),
`a = [5, 9]`:

| call | expected | JIT | interpreter |
|---|---|---|---|
| `g1(true, 3)` | 3 | 3 | — |
| `g1(false, 3)` | 7 | **0** | **nil** (`nil is forbidden by the non-optional return contract`) |
| `g2(true, a)` | 9 | **3** | — |
| `g2(false, a)` | 7 | **0** | — |
| `if c: 7 else: a[1] as i64` | ok | ok | ok |
| `if c: (a[1] as i64) else: 7` | ok | ok | ok |

A cast only in the ELSE arm, or a parenthesized THEN-arm cast, is correct.

## Impact found

`src/compiler/70.backend/linker/elf_parser.spl:283-284` read ELF symbol
`st_info`/`st_other` with this form, so every ELF64 symbol parsed with binding
LOCAL and no global entered the resolver. The internal ELF engine therefore
failed every link with `entry symbol not defined: _start` — first seen as the
SimpleOS x86_64 user internal link failure from the pure-Simple Stage 2
candidate (built from `release/1.0` `a5cda768103`), which shows the pure-Simple
compiler path is affected too, not only the seed.

Fixed by parenthesizing the cast arms in the 6 linker sites
(`elf_parser.spl`, `elf/stream_emit.spl` x2, `elf/archive_file.spl`,
`elf/elf_file_reader.spl`); regression spec
`test/01_unit/compiler/backend/linker/simpleos_internal_entry_spec.spl`.

## Remaining unfixed call sites (same form, outside the linker)

`grep -rnE "if [^:]+: [^()]+ as [a-z0-9]+ else:" src/` lists ~25 more, e.g.
`src/os/sosix/process.spl:141`, `src/os/kernel/ipc/syscall_ipc.spl:113`,
`src/lib/skia/feature/glyph/subpixel.spl:33-55`,
`src/lib/nogc_async_mut/link_working_set/file_store.spl:173`,
`src/lib/gc_async_mut/gpu/engine2d/draw_ir_box_effects.spl:302-305`.
Each is a latent miscompile until the parser/lowering is fixed.

## Fix direction

Find where the `as` type operand is parsed inside an inline-if THEN arm (Rust
seed parser and the pure-Simple parser both) and stop it from consuming or
mis-associating the following `else:`; then add a parser spec with the table
above and drop the parenthesized workarounds.
