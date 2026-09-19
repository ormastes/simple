# Internal ELF link engine — performance, 2026-09-19 (lane C4)

Plan: `doc/03_plan/compiler/linker/mold_mdsocpp_linker_plan_2026-09-18.md` §11–§12.
Lane C4 measures and speeds up the pure-Simple ELF engine
(`src/compiler/70.backend/linker/elf/`, `reloc_engine.spl`, `elf_parser.spl`).

## How this was measured

```bash
sh scripts/perf/bench-elf-link.shs [--runs N] [--only static|pie|dynamic|synth]
```

The harness links four inputs with the internal engine, `ld.lld-23` and `mold`,
and records for each: median wall time and max RSS over N runs
(`/usr/bin/time`), the output's sha256, and whether the output actually RUNS
(every fixture exits 42). It prints the `bin/simple` identity (`readlink -f`,
size, mtime, sha256, `--version`), the host and its load average, and the
linker versions before any timing, because none of these numbers are
comparable without them. The internal row additionally reports `elf_link=`,
the in-process time of `elf_link` itself as measured by
`scripts/perf/elf_link_bench.spl`, which excludes the fixed interpreter
startup.

Inputs: the three A7 fixtures (static, static PIE, dynamic against the host
glibc) plus `synth`, a generated corpus of `SYNTH_N` (default 200) clang
objects chained through `f_0 … f_N`, 12 noinline helpers and a 64-entry global
array each — 3.2 MB of input, a ~1.3 MB `.text` and a 698 KB output.

Environment for every number below: aarch64, 20 CPUs, a SHARED box — the final
"after" run reported `load 17.32 21.58 16.18`, the earlier baseline runs
`load 5.18 3.08 2.83`, and that difference alone moves wall time by a factor of
two (the same static fixture measured 0.40 s at load 5 and 1.08 s at load 17,
with `elf_link` unchanged at 11-12 ms). Treat wall time as an envelope and
`elf_link` ratios as the signal. `bin/simple` =
`/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple`,
51,607,912 bytes, mtime 2026-09-19 09:09:30, sha256 `350328bab5142ff4…`,
`Simple Language v1.0.0-beta.12` — **the Rust bootstrap seed, running the
engine in its interpreter** (see "Native execution is blocked" below).
`ld.lld` is LLVM 23.1.0, `mold` from `~/.local/bin`.

## Before / after

`elf_link` is the engine time; `wall` is the whole process including ~0.35 s of
interpreter startup and, for `synth`, the bench driver's own byte conversions.
Baseline = `7c875a81067`, after = this lane's two commits.

The "after" column is ONE harness run at `b7f472dfc2b`, `--runs 3`, load
17.32; the "before" column is the same driver against a checkout of
`7c875a81067`, at the lower load noted above.

| input | metric | before | after | ld.lld-23 | mold |
|---|---|---|---|---|---|
| static fixture (2 objs) | `elf_link` | 12 ms | 11 ms | — | — |
| | wall / RSS | 0.40 s / 158 MB | 1.08 s / 140 MB | 0.00 s / 23 MB | 0.01 s / 21 MB |
| PIE fixture (2 objs) | `elf_link` | 13 ms | 11 ms | — | — |
| | wall / RSS | 0.42 s / 162 MB | 1.06 s / 152 MB | 0.00 s / 24 MB | 0.00 s / 21 MB |
| dynamic fixture (4 objs + libc.so.6) | `elf_link` | 388 ms | **284 ms** (220 ms at load 5) | — | — |
| | wall / RSS | 0.78 s / 166 MB | 0.85 s / 159 MB | 0.00 s / 25 MB | 0.01 s / 21 MB |
| synth 20 objects | `elf_link` | 38.05 s | **0.36 s** (106x) | — | — |
| synth 50 objects | `elf_link` | 227.27 s | **0.82 s** (278x) | — | — |
| synth 200 objects | `elf_link` | 4291.05 s (71.5 min) | **4.46 s** (962x; 3.62 s at load 5) | — | — |
| | wall / RSS | 4292.86 s / 574 MB | 6.23 s / 522 MB | 0.00 s / 27 MB | 0.01 s / 23 MB |

The baseline grows quadratically in input size (38.05 s at 20 objects,
227.27 s at 50, 4291.05 s at 200 — exponent 1.95 over the 2.5x step and 2.10
over the 4x step); the engine after this lane grows roughly linearly
(0.36 s -> 0.82 s -> 4.46 s for 20 -> 50 -> 200).

Trap for anyone re-running the baseline: the first 200-object attempt was
KILLED at 1,325 s by this host's CPU watchdog —
`kill_simple_monitor … age=1325s >= budget=900s while pegged above 95% CPU`.
The measured 4291 s run needed `SIMPLE_TIMEOUT_SECONDS=0` in the measured
process's own environment, and was run from a throwaway detached worktree at
`7c875a81067` so the lane's own tree stayed at HEAD.

Byte-identical outputs, before and after, for every input — including the
71-minute baseline 200-object link (sha256, first 16 hex): static `cfd7235c285f5ca5`, PIE `4aef985c972e44cb`, dynamic
`b1a7044961f4fa9f`, synth-20 `51373e104c901b2c`, synth-200 `32405fe5d2d28022`.
Every output still runs and exits 42 (the dynamic one prints
`hi from libc`).

The engine is still 100x+ slower than ld.lld/mold and uses ~25x their memory.
That gap is now dominated by the interpreter and by the `[i64]`-per-byte
representation, not by algorithmic blowup in the engine — see "What is left".

## Where the time went (interpreter sampling profiler)

`SIMPLE_INTERP_SAMPLE=1 SIMPLE_INTERP_SAMPLE_US=… SIMPLE_INTERP_SAMPLE_OUT=…`
on the synth-20 and synth-200 links.

| stage | top frame (self %) |
|---|---|
| baseline, synth-20 | `patch_u32_le` **97.43%** |
| after fix 1, synth-200 | `patch_u32_le` 47.20%, `write_u64_le` 21.87%, `write_u32_le` 12.17%, `write_bytes` 9.53% |
| after fixes 1–2, synth-200 | `elf_static_contents` 13.84%, `elf_append_symtab` 10.06%, `elf_build_symtab` 6.08%, `elf_write_image` 5.87% |
| baseline, dynamic fixture | `elf_strtab_get` 26.50% + `char_from_code(_inline)` 33.50% (→ `elf_parse_shared` 87% inclusive) |

### Fix 1 — relocation patching rebuilt the whole section, per relocation

`patch_u32_le` / `patch_u64_le` (`reloc_engine.spl`) built a NEW array element
by element, with a 4/8-way branch chain per byte, to change 4 or 8 bytes. That
is O(section bytes) per relocation: quadratic in (section size × relocation
count). They now write the target bytes in place. An offset fully past the end
still returns the buffer unchanged, as the rebuild loop did by never matching.
One case DID change, deliberately: a site that STRADDLES the end
(`offset < len < offset + width`) used to get a partial prefix written and now
gets nothing — a straddling relocation is a malformed input either way, and a
half-written site is the worse of the two.

The static link driver's relocation loop was also restructured
section-outer/relocation-inner, so each output section's buffer is taken out of
`contents` once rather than being handed to — and returned from — a patch
helper per relocation. The relocated value and the AArch64 instruction-field
merge still come from the reloc_engine oracle, now exposed as
`reloc_patch_width` / `reloc_patch_word`, which `reloc_patch_bytes` itself uses,
so there is exactly one definition of that merge.

### Fix 2 — every append copied the whole image

The measured cause, in the seed interpreter (`/tmp` microbenchmark, same
binary):

| appends | inline `b = b.push(x)` | `b = helper(b, x)` |
|---|---|---|
| 5,000 | 0.19 ms | 223 ms |
| 20,000 | 0.70 ms | 2.81 s |
| 80,000 | 3.27 ms | 102.06 s |

Passing a buffer to a function and storing its return value copies the buffer
(verified separately: `var r = b; r[0] = 9` leaves the caller's array
untouched). Every `b = write_u64_le(b, …)` / `write_bytes` / `write_zeros` /
`elf_sym_entry` / `elf_rela_entry` in the image path therefore copied the whole
image — quadratic in output size. `elf_write_image`, `elf_append_symtab`,
`elf_build_symtab`, `elf_static_contents` and the GOT/`.rela` builders now
append inline and call the record encoders on an EMPTY buffer, so each encoder
returns only its own record and remains the single encoding definition.

### Fix 3 — ELF names were decoded one character at a time

`elf_strtab_get` built each name with `result = result + char_from_code(b)`.
Decoding `libc.so.6`'s `.dynstr` that way was 60% of a dynamic link. ASCII
names (every ELF name in practice) now go through one `bytes_to_text` runtime
byte copy via the sanctioned `std.string_core` provider — no direct `rt_*` call
is added to `src/compiler/**`, so the `check-no-direct-rt` ratchet is
unaffected. A byte ≥ 0x80 keeps the old per-character path, so that behaviour
is unchanged.

## Verification

- Output equality is the regression gate: every fixture's sha256 is unchanged
  before/after (listed above), and every output still runs (exit 42).
- 28 specs, one `bin/simple test --no-session-daemon <spec>` each, reading
  `SPEC FILE VERDICT`. **28/28 `outcome=OK`, 415 assertions executed, 0
  failed, 0 skipped, 0 dropped.** All 24 under
  `test/01_unit/compiler/backend/linker/` — `archive_parser` 27,
  `boot_layout_ops` 17, `boot_layout_plan` 25, `elf_archive_closure` 5,
  `elf_boot_link` 25, `elf_dynamic_link` 7, `elf_exec_writer` 4,
  `elf_gnu_hash` 6, `elf_got_static` 7, `elf_parser` 16,
  `elf_reloc_target_section` 4, `elf_section_header_field_parity` 4,
  `elf_static_link` 6, `elf_static_pie` 5, `elf_symtab` 6, `elf_writer` 18,
  `elf_x64_dynamic` 7, `link_corpus_recipe` 6, `link_engine_external` 15,
  `linker_dead_imports` 9, `linker_script` 51, `native_linking_internal` 5,
  `reloc_engine` 60, `sym_resolver` 20 — plus the four reloc-engine consumers
  `loader/loader_reloc_oracle` 9, `loader/loader_reloc_wire4` 5,
  `loader/reloc_apply` 11, `linker/gpu_smf/smf_reloc_formulas` 32.
- `bin/simple lint` on the two smaller changed files: `reloc_engine.spl`
  0 errors / 11 warnings and `elf_parser.spl` 0 errors / 2 warnings, with
  every warning pointing at OTHER files (`export use *` style in
  `src/lib/**` and `src/compiler/{10.frontend,35.semantics,90.tools}/**`),
  none at a changed line. `elf_static_link.spl` (1,120 lines) and
  `elf_exec_writer.spl` were not linted: per
  `.claude/rules/commands.md` the linter's cost is superlinear in file
  content and a file this size exceeds the practical budget on this host.

## Native execution is blocked — two separate blockers

**(a) The in-process JIT refuses the module.** With
`SIMPLE_JIT_STAGE_TRACE=1 SIMPLE_JIT_SYMBOL_TRACE=1` on the static fixture:

```
[jit-stage] compile_all:start functions=394 globals=683
[jit-stage] compile_all:done compiled=394
[jit-fallback] unresolved external symbol 'elf_link': whole module dropped to
  the interpreter (expect ~100-1000x slowdown). Set SIMPLE_JIT_STRICT=1 …
[INFO] JIT compilation failed … Module error: unresolved external symbol
  'elf_link' would NULL-jump in JIT; deferring to interpreter
```

So the JIT compiles all 394 functions of the flattened unit and then discards
the module because the imported `elf_link`
(`compiler.backend.linker.elf.elf_static_link`) is not among its defined
symbols. Every number in this file is therefore an INTERPRETED number, and so
is every linker spec run. Fixing that cross-module resolution is a seed/JIT
change, outside this lane.

**(b) `native-build` refuses.** A native speed run was attempted:

```
SIMPLE_BOOTSTRAP=1 bin/simple native-build scripts/perf/elf_link_bench.spl
  -> SCV-E-ADMISSION: compile-event-journal-missing
SIMPLE_BOOTSTRAP=1 SIMPLE_SCV_INVENTORY_COLD_INIT=1 … native-build …
  -> SCV-E-SNAPSHOT: snapshot-inventory-empty
     error: native-build: SCV freeze has no admitted source inventory to freeze
     the entry closure against … Refusing to compute an entry closure under the
     default fail-closed policy.
     Error: native-build entry closure is empty (source snapshot unavailable)
```

The error message's own opt-in was then tried, as a feasibility probe (not for
a comparable number — it weakens the consistency guarantee):

```
SIMPLE_BOOTSTRAP=1 SIMPLE_SCV_FREEZE_FALLBACK=1 … native-build …
  -> SCV-E-ADMISSION: filesystem-event-journal-missing   (exit 2)
```

So the fallback is refused too, and there is no path to a native engine binary
from this checkout without first populating an SCV inventory/journal. That is
the precise blocker; it is the same SCV admission family already recorded for
lane A3 in the plan §9.

## What is left (not fixed here)

1. **`[i64]`-per-byte buffers.** Every image byte is a boxed 64-bit array
   element; the 698 KB synth output costs 543 MB RSS. Moving the engine's
   buffers to `[u8]` is the single biggest remaining win, and is a wide
   refactor across `elf_writer`, `elf_exec_writer`, `elf_static_link`,
   `synthetic_sections` and `reloc_engine`. Not attempted in this lane.
2. **`elf_boot_link.spl`** (lane B1's kernel linker) still applies relocations
   through `contents[ok] = reloc_patch_bytes(…)`. It gets fix 1's in-place
   write, but not the section-outer restructuring; its buffer is still copied
   once per relocation.
3. **`elf_parse_string_table`** copies a whole string table byte by byte per
   object, and `elf_static_contents` copies input section bytes the same way
   (13.8% of synth-200 after the fixes).
4. **No bulk array primitive.** There is no `[i64]`/`[u8]` slice-append in
   `std` that avoids the per-element loop; every "bulk" copy in this engine is
   still an interpreted per-element push. A bulk `extend`/`slice` provider
   would remove most of what remains.
