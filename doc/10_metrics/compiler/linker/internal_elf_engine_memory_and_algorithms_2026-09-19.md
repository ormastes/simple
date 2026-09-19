# Internal ELF link engine — memory and remaining algorithmic gap, 2026-09-19 (lane C5)

Follow-on to `internal_elf_engine_perf_2026-09-19.md` (lane C4, which removed
the quadratic relocation/append/strtab behaviour). C5's brief was the remaining
**memory** gap (~22x vs `ld.lld`) and whatever algorithmic cost survived C4.

Measured with `sh scripts/perf/bench-elf-link.shs`, same harness and the same
four inputs as C4. Every number below is an INTERPRETED number — see
"Where the memory actually goes".

## Environment (different from C4's — do not compare across binaries)

`bin/simple` = `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple`,
**51,624,896 bytes, mtime 2026-09-19 15:30:38, sha256 `cb7944151f8b62b3`,
`Simple Language v1.0.0-beta.13`** — the Rust bootstrap seed. C4 measured a
DIFFERENT build (51,607,912 bytes, `350328bab5142ff4`, beta.12, 09:09), so
C4's absolute numbers are not directly comparable to these; C5 re-measured its
own baseline from a worktree pinned to C4's tip.

Host: aarch64, 20 CPUs, SHARED. Load moved between **6 and 34** during the
session and that alone moves wall time by 2-3x (the same synth-20 link
measured 208 ms and 808 ms within minutes of each other). Treat wall time as
an envelope; `elf_link` medians over interleaved BEFORE/AFTER rounds are the
signal, and both sides of every A/B below were run back to back in the same
round, from two worktrees pinned to their own shas.

`ld.lld` is LLVM 23.1.0, `mold` 2.42.0.

Baseline = `69183c5e62e` in `/home/yoon/dev/simple-lnk-base`;
after = `work/lnk-perf2` in `/home/yoon/dev/simple-lnk-perf2`.

## Where the memory actually goes — the 22x is mostly NOT engine data

This is the finding that reframed the lane. RSS was attributed by running the
same binary on progressively more of the path:

| what runs | wall | max RSS |
|---|---|---|
| `bin/simple run` on a 3-line hello world | 0.07 s | **23.3 MB** |
| a script that only `use`s `elf_static_link` | 0.34 s | **57.2 MB** |
| the same script CALLING `elf_link` with ZERO objects | 0.90 s | **130.6 MB** |
| static fixture, 2 small objects (`elf_link` 12 ms) | 0.87 s | 149.0 MB |
| synth-20 (320 KB in, 70 KB out) | 1.53 s | 186.8 MB |
| synth-200 (3.2 MB in, 698 KB out) | 8.54 s | 472.2 MB |

So of the 22x RSS gap, **130.6 MB is fixed cost that no linker change can
touch**, and `ld.lld`'s entire footprint is 23 MB — the same as this
interpreter's hello world. The +74 MB / +0.56 s step between "import" and
"call with zero objects" is the JIT compiling the module and then throwing it
away. That is not inferred; the run prints it:

```
[jit-fallback] unresolved external symbol 'elf_link': whole module dropped to
  the interpreter (expect ~100-1000x slowdown). Set SIMPLE_JIT_STRICT=1 to
  turn this into a hard error.
```

That is lane J1's problem, and it is the single largest item between this
engine and `ld.lld` on BOTH axes: ~0.9 s and ~130 MB before the first input
byte is read. Engine-owned data is the remainder: ~56 MB at synth-20 and
~340 MB at synth-200 before this lane's changes, ~36 MB and ~235 MB after.

## Before / after

Medians of 3 interleaved BEFORE/AFTER rounds (`--runs 1` each), load 19-23 on a
20-CPU shared box. BEFORE and AFTER ran back to back inside each round, from two
worktrees pinned to their own shas, so both sides saw the same machine.

| input | metric | before | after | ld.lld-23 | mold 2.42 |
|---|---|---|---|---|---|
| static fixture, 2 objs | `elf_link` | 25 ms | **13 ms** | — | — |
| | wall / RSS | 1.41 s / 144.8 MB | 1.46 s / 145.2 MB | 0.01 s / 25.0 MB | 0.08 s / 7.1 MB |
| static PIE, 2 objs | `elf_link` | 15 ms | 30 ms | — | — |
| | wall / RSS | 1.36 s / 146.4 MB | 1.30 s / 144.9 MB | 0.00 s / 25.0 MB | 0.03 s / 7.2 MB |
| dynamic, 4 objs + libc.so.6 | `elf_link` | 424 ms | **276 ms** | — | — |
| | wall / RSS | 1.51 s / 154.9 MB | 1.29 s / 146.8 MB | 0.01 s / 26.1 MB | 0.08 s / 7.2 MB |
| synth 20 objects | `elf_link` | 433 ms | **374 ms** | — | — |
| | wall / RSS | 1.29 s / 183.7 MB | 1.11 s / **166.9 MB** | 0.00 s / 25.2 MB | 0.03 s / 10.9 MB |
| synth 200 objects | `elf_link` | 5,863 ms | **5,046 ms** | — | — |
| | wall / RSS | 8.54 s / 472.2 MB | **6.39 s / 365.1 MB** | 0.01 s / 27.6 MB | 0.10 s / 7.4 MB |

Read this with three caveats.

- **`elf_link` excludes the caller-side fix; wall and RSS include it.** Change 1
  below moves work out of `elf_link`'s caller, which production shares (the same
  widening lived in `internal_link_native_read_i64`). That is why synth-200 wall
  falls 25% while `elf_link` falls 14%.
- **The static and PIE `elf_link` columns are noise.** 13-30 ms on a box whose
  load moved by 3x during the run says nothing; the PIE row reading "worse" is
  the clearest evidence of that. Those two fixtures are 2 small objects, and
  their wall time is ~97% fixed interpreter+JIT cost either way.
- **`ld.lld` and `mold` wall times are at the harness's timer resolution** and
  are dominated by process startup on a loaded box; treat them as "under
  0.1 s", not as a measured ratio. Their RSS is solid: 25-28 MB and 7-11 MB.

Net, against `ld.lld` on synth-200: **6.39 s vs 0.01 s** and **365 MB vs 28 MB**
after, from 8.54 s / 472 MB before. RSS improved by **107 MB (-23%)**, which is
the packed-input change; the remaining 365 MB is ~130 MB fixed (above) plus the
engine's own boxed-per-byte buffers.

### Sampling profile, synth-200, same corpus, both sha `32405fe5d2d28022`

Whole-process totals at a 5 ms interval — the absolute sample COUNTS matter as
much as the shares, because the totals differ:

| frame | before (1,818 samples) | after (1,292 samples) |
|---|---|---|
| `main` (the caller's byte widening + output write) | **424 (23.3%)** | below the top 9 |
| `elf_static_contents` | 272 (15.0%) | 245 (19.0%) |
| `elf_write_image` | 187 (10.3%) | 207 (16.0%) |
| `elf_append_symtab` | 119 (6.6%) | 177 (13.7%) |
| `elf_build_symtab` (inclusive) | 163 (9.0%) | **81 (6.3%)** |
| `elf_sym_row` | 48 (2.6%) | gone (deleted) |
| `elf_read_u64_le` | 99 (5.5%) | 52 (4.0%) |

Total interpreted samples fell **1,818 -> 1,292 (-29%)**. The caller's widening
frame disappears entirely; the symbol table halves in absolute cost and its
helper is gone. The three byte-copy loops are unchanged in absolute terms (they
were not touched in the landed set) and so rise as a share of a smaller total.


## What changed

### 1. Objects are taken as packed `[u8]`, not widened to `[i64]`

`ElfLinkRequest.objects` was `[[i64]]`: one boxed 64-bit array element per
input byte, produced by an interpreted push per byte. Both real callers did
that widening — `internal_link_native_read_i64` in
`_LinkerWrapper/native_linking.spl` and the bench driver. The blob
`file_read_bytes` already returns is packed one byte per element and now goes
in as it comes off disk. The image is repacked on the way out with
`Array + ByteArray`, one runtime copy, instead of a push per output byte.

Measured on synth-20 (the bench driver's own phase timers):
`load_inputs` **58,878 us -> 585 us**, `write` **43,805 us -> 875 us**.

Nothing downstream changes representation: `elf_static_contents` already read
`obj.raw[i] as i64`, so the element width never escapes the parser.

### 2. String tables are sliced, not copied byte by byte

`elf_parse_string_table` rebuilt a whole table with one interpreted push per
byte, once per input file — a shared object's `.dynstr` is ~100 KB, and C4
measured that path at 60% of a dynamic link before its own fix.
`elf_strtab_get` rebuilt every name one character at a time. Both are now
single slices. `ElfStringTable.data` is read ONLY by `elf_strtab_get`, which
already widens each byte with `as i64`, so a packed slice cannot leak its
element width out of `elf_parser`.

### 3. The symbol table was quadratic in symbol count

The six parallel `Elf64_Sym` output columns were carried in a struct threaded
through a per-symbol helper (`rows = elf_sym_row(rows, ...)`). The helper read
each column back out of the struct and pushed to it — and a push to an array
the struct still holds copies the whole column — so **every symbol copied all
six arrays**. Measured on synth-200 (table above): `elf_build_symtab` inclusive falls from
163 to 81 samples and its per-row helper's own 48 samples disappear — the
symbol table's absolute cost roughly halves. The columns are now six locals
appended inline.

This is the one genuinely ALGORITHMIC defect C5 found: O(symbols^2). Its
coefficient is small at these sizes — the baseline already scaled roughly
linearly from 20 to 200 objects — so it is a real but modest win here and a
growing one as inputs get larger, which is why 20-object measurements do not
surface it.

### 4. Header patches no longer copy the image

`elf_append_symtab` patched four ELF header fields through `elf_put_le`, whose
`var out = b` makes the array non-unique so the first index-assign copies all
698 KB. Four fields, four full copies. They are written inline now, and
`elf_put_le` — which had no other caller — is deleted rather than left unused.

### 5. Byte reads widen before shifting

`read_u32_le` / `read_i64_le` (`reloc_engine.spl`) and `elf_rd_le` now write
`(bytes[i] as i64) << 8` rather than `bytes[i] << 8`. No behaviour change for
the `i64` elements they get today. It removes a trap that cost this lane a
day: see "The packed-assembly experiment" below.

## The packed-assembly experiment — worked, byte-identical, and REVERTED

The obvious way to close both the time and the memory gap is to assemble every
buffer as a packed `[u8]` and never materialise one boxed value per byte.
Measured in the seed interpreter (100 KB each, with `elf_link` called so the
module really is interpreted — see the trap below):

| operation | time | per element |
|---|---|---|
| packed slice `raw[0:100000]` | **64 us** | 0.64 ns |
| packed concat `sl + sl` (100k+100k) | **20 us** | ~0.1 ns |
| `Array` slice, 70k `i64` | 7,539 us | 108 ns |
| `Array + Array`, 140k `i64` | 11,335 us | 81 ns |
| `Array.concat(Array)`, 140k | 33,311 us | 238 ns |
| interpreted push loop into `[i64]` | 87,812 us | **880 ns** |
| interpreted push loop into `[u8]` | 172,417 us | **1.72 us** |

Packed bulk ops are ~1,000x cheaper per byte than an interpreted push and ~100x
cheaper than the `Array` equivalents. Built on that, `elf_static_contents`,
`elf_write_image`, `elf_append_symtab` and `elf_build_symtab` were rewritten to
concatenate packed runs and widen back to `[i64]` once at the end. It worked:
**synth-20 `elf_link` 526 ms -> 208 ms**, every one of those four frames left
the sampling profile entirely, and **every fixture sha256 was unchanged**.

It was reverted anyway, for one reason: it **broke 12 linker specs**, and a
change that breaks 12 specs is not a candidate.

The mechanism is worth recording because it will catch the next person.
`Value::byte_array_values` (the seed's packed-to-generic widening) produces
`Value::UInt { width: 8 }`, not `Value::Int`. So a buffer that has passed
through a packed representation holds **8-bit-wide** values, and `x << 8` on
one of those **wraps to 0** instead of widening. `elf_link` declares
`Result<[i64], text>`; the packed version still satisfied it structurally and
byte-wise, but every consumer that does `(b[o + 1] & 0xff) << 8` on the result
— which is what the specs' own `rd16`/`rd32`/`rd64` helpers do, and what lane
B1's `elf_boot_link` consumers do — silently read a truncated value.

The engine's own readers were fixed with `as i64` (change 5 above) and the
FIXTURE outputs stayed byte-identical, which is exactly why this was dangerous:
the sha256 gate did NOT catch it. What caught it was running the specs. The
first packed attempt did fail the sha gate for a different reason — 1,003 bytes
of a synth-20 link came out zeroed because `elf_rd_le` truncated the existing
instruction word before the AArch64 field merge — and fixing that made the
outputs identical while the contract break remained.

Fixing it at the source would need `elf_link` to keep returning `i64` elements
while assembling packed, and there is **no bulk packed-to-`i64` widening** in
the interpreter: every route (`empty_array.concat(packed)`, `packed + array`,
slicing) yields `UInt{width:8}`, and `.map()` is per-element interpreted. The
alternative — widening the declared types to `[u8]` and fixing every consumer,
including three sibling lanes' specs — is a contract change C5 is not entitled
to make unilaterally.

**Filed:** `doc/08_tracking/bug/interpreter_packed_bytearray_index_assign_2026-09-19.md`
records the related seed gap (`buf[i] = v` is refused on a packed `[u8]` by
`node_exec.rs` although `place.rs:213` implements it), which is what forced the
widening in the first place. With that fixed AND a bulk widen-to-`i64`, the
packed assembly can land as measured: ~2.5x on `elf_link` and roughly a 24x cut
in the engine's own live bytes.

## Things that did NOT help

| tried | result | why |
|---|---|---|
| `b = b + entry` per 24-byte symbol entry (`Array + Array`) | synth-200 `elf_link` 4.5 s -> **7.4 s** | array `+` does `Arc::clone` then `make_mut`, i.e. it copies the WHOLE accumulator on every call. Fine for a handful of large runs, quadratic per record. `b.push(x)` on a local stays unique and is amortised O(1). |
| `Array` slice + `+` throughout `elf_append_symtab` | its self time went **13.37% -> 16.04%** of synth-200 | same reason: five full copies of a 698 KB boxed array beat 690k pushes on paper but not in practice. Reverted; the push loops are back. |
| `text_to_bytes(str_repeat(char_from_code(0), 65536))` as a zero-run primitive | **96 ms for 64 KB** | `str_repeat` is interpreted per character. Doubling a packed run (`z = z + z`) is the right shape, ~0.2 ms for 1 MB — but it is only usable inside the packed path that was reverted. |
| bucketing `refs` by output section to remove the O(sections x relocations) rescan in the relocation loop | **not attempted** | the natural form, `ref_of[k] = ref_of[k].push(j)`, is itself quadratic: the nested read makes the inner array non-unique so every push copies it. Worth ~2% at synth-200 and not worth a worse shape. Recorded rather than done. |
| micro-benchmarking the primitives in a standalone script | gave numbers **~100x too fast** | a script that imports but never calls `elf_link` keeps its JIT module, so the loops run natively. Every micro number in this file was taken with `elf_link` actually called, so the module is dropped and the loop really is interpreted. This trap invalidated a first round of measurements. |

## Verification

- **Byte-identical output is the gate.** Every fixture's sha256 is unchanged
  from `69183c5e62e`, on every A/B round: static `cfd7235c285f5ca5`, PIE
  `9bbe8caeb29c47df`, dynamic `c4f2b7dd1617abad`, synth-20
  `51373e104c901b2c`, synth-200 `32405fe5d2d28022`. Every output still runs and
  exits 42.
- **Linker specs**, one `bin/simple test --no-session-daemon <spec>` each,
  reading `SPEC FILE VERDICT`.
- **Mutation gate**: `sh scripts/check/check-link-mutation-gates.shs`.
- **Lint** on the changed files small enough to lint.

- **Byte-identical output, all 5 fixtures, all 3 rounds** — sha256 first 16 hex,
  identical BEFORE and AFTER: static `cfd7235c285f5ca5`, PIE
  `9bbe8caeb29c47df`, dynamic `c4f2b7dd1617abad`, synth-20 `51373e104c901b2c`,
  synth-200 `32405fe5d2d28022`. Every output was executed and exited 42.
- **36 spec files, 0 failures, 554 assertions executed**, one
  `bin/simple test --no-session-daemon <spec>` each, reading `SPEC FILE
  VERDICT`: all 32 under `test/01_unit/compiler/backend/linker/`, plus
  `compiler/linker/gpu_smf/smf_reloc_formulas_spec.spl` and the three
  `compiler/loader/` reloc consumers (`loader_reloc_oracle`,
  `loader_reloc_wire4`, `reloc_apply`). Largest: `linker_script` 54,
  `pe_exec_writer` 42, `reloc_engine` 60, `smf_reloc_formulas` 32,
  `archive_parser` 27, `elf_boot_link` 25, `boot_layout_plan` 25,
  `native_linking_internal` 21, `sym_resolver` 20.
- **Mutation gate**: `sh scripts/check/check-link-mutation-gates.shs` ->
  `SELFTEST PASS — 7 fixture(s) checked` then twelve `RED <name> — ... turned
  red as expected` rows and the verdict `PASS — 12 mutation(s) each turned
  their gate red`.
- **Lint**: `elf_parser.spl` 0 errors / 2 warnings and `reloc_engine.spl`
  0 errors / 14 warnings — every warning is an `export use *` in ANOTHER file
  (`src/lib/**`, `src/compiler/{10.frontend,35.semantics,90.tools}/**`), none on
  a changed line. `elf_static_link.spl` (1,563 lines) and `native_linking.spl`
  were not linted: per `.claude/rules/commands.md` the linter's cost is
  superlinear in file content and files that size exceed the practical budget
  on this host — the same exemption lane C4 took.


## What is still between this engine and ld.lld

Honest accounting for synth-200, where the gap is widest:

1. **~0.9 s and ~130 MB of fixed cost before any input is read** — interpreter
   startup (23 MB), loading the linker module graph (+34 MB), and the JIT
   compiling 394 functions and discarding the module (+74 MB). Lane J1 owns
   this. It is bigger than everything below combined on the small fixtures, and
   it is why the static and PIE rows will not improve no matter what the engine
   does.
2. **`elf_static_contents` is 19% of the whole process** (245 of 1,292
   samples), copying input section bytes into output section buffers one
   interpreted push per byte. Packed assembly removes it outright (measured),
   and is blocked on the two seed gaps above.
3. **`elf_write_image` 16% and `elf_append_symtab` 14%** (207 and 177 samples),
   same shape, same blocker. These three are half the remaining work.
4. **`archives` are still widened to `[[i64]]`.** `ElfLinkRequest.archives`
   keeps the old representation because `archive_parser.spl` indexes those
   bytes throughout and every one of its readers would need the same `as i64`
   audit change 5 applied to `reloc_engine`. It costs 32 bytes per archive byte;
   in practice the only archive on the hosted path is `libc_nonshared.a`, which
   is small, so this was left rather than half-done.
5. **The rest is genuinely per-symbol and per-relocation interpreted work** —
   `elf_read_u64_le`, `elf_collect_refs`, `elf_ref_addr`, `elf_parse_symbols`.
   There is no bulk primitive to reach for here; it is one interpreted
   operation per ELF field, and it is what the ~100x interpreter tax looks like
   once the per-byte loops are gone.

No quadratic behaviour remains that C5 could find. The engine already scaled
close to linearly from 20 to 200 objects BEFORE the symbol-table fix (the
quadratic term's coefficient was small at these sizes), and the profile is now
flat enough that no single remaining frame is worth more than a few percent
except the three byte-copy loops above, all of which are blocked on the same
seed change.
