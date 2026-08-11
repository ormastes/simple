# Fabricated-stub guard failed OPEN on unbaselined symbols

**Date:** 2026-08-09
**Status:** FIXED (gate added); one real finding left RED on purpose
**Severity:** data loss in a shipped SimpleOS guest
**Gate:** `scripts/check/check-simpleos-fabricated-rt-elf.shs`
**Accounting:** `config/simpleos_fabricated_rt_elf_accounting.sdn`
**Spec:** `test/01_unit/os/kernel/boot/simpleos_fabricated_rt_elf_gate_spec.spl`

## The incident

`rt_index_of` reached the shipped x86_64 WM kernel as a WEAK stub whose entire
body is `xor %eax,%eax; ret` — a constant 0. `index_of` returned 0 instead of
11. Every caller guards with `if idx > 0:`, so a constant 0 reads as NOT FOUND,
and all 45 `:root` CSS custom properties were dropped in the guest. Measured on
the same receiver in the same run:

    raw_len=15 line_len=15 colon_index_of=0 colon_find_from=11

Fixed at `1f1c00aa578afc765b996a5b6aa8208c2756e361` by defining it in
`examples/09_embedded/simple_os/arch/x86_64/boot/baremetal_stubs.c`.

**Causal chain.** `("index_of", 1)` was added to cranelift's
`is_bare_builtin_collection_method` allowlist on 2026-08-01, routing bare
`.index_of(needle)` calls to the runtime symbol `rt_index_of`. No arch stub file
ever defined that symbol. The x86_64 freestanding link pulls
`examples/09_embedded/simple_os/arch/x86_64/boot/auto_stubs.c`, which fabricates
~4,023 WEAK zero-returning definitions for any unresolved `rt_*`, so instead of
the link failing, a body was FABRICATED.

## The guard defect

`simpleos_check_no_fabricated_rt_stubs`
(`src/compiler/70.backend/backend/llvm_native_link.spl`) compares an entry's
fabricated set against `config/simpleos_fabricated_rt_baseline.sdn`.
`rt_index_of` was never in that baseline, and nothing fired.

The structural problem is the direction of enumeration. The check starts from a
list of *already-suspicious* names and asks whether reality matches. A NEW
fabrication — the only kind that matters, because a known one is by definition
already recorded — is invisible to that shape. It fails OPEN.

## The fix: enumerate from the artifact

`scripts/check/check-simpleos-fabricated-rt-elf.shs` inverts the direction. It
reads the LINKED kernel ELF, which cannot lie about what shipped:

1. `nm` enumerates every `rt_*` symbol actually present.
2. Each is classified **by body**, never by linkage or by name. A constant
   return is fabricated whether it is a `W` symbol from `auto_stubs.c` or a
   strong `T` hand-written `return NIL_VALUE;`. Weak linkage does not imply
   fabricated: `rt_memcpy`, `rt_memset` and the `rt_dma_*` family are
   `__attribute__((weak))` with real loops.
3. Every constant-return body must carry a row in the accounting file **with a
   written justification**. A row without a reason is rejected — accounting
   without a reason is just an allowlist, and an allowlist is what let this
   through.
4. A symbol nobody has written about is unaccounted, hence a FAILURE. Nobody
   has to predict it in advance.

### Fail-closed details that are load-bearing

- **Empty symbol set is ERROR, never PASS.** No ELF, no `nm` output, no
  disassembly, or zero `rt_*` symbols all exit 2. This repo has a documented
  family of gates that reported success over zero items; this is not another.
- **A passing verdict states its count**: `PASS — <n> symbol(s) checked ...`,
  matching `.claude/rules/vcs.md`. `FAIL — ...` is exit 1, `ERROR — nothing was
  checked` is exit 2.
- **Decode ambiguity resolves fail-closed.** The SimpleOS x86 kernels carry
  64-bit code under an ELF32 / `Intel 80386` header (multiboot). Under an i386
  decode the REX prefix of `push %rbp` disassembles as a spurious `dec %eax`,
  which makes a fabricated stub look like real work. The gate therefore
  disassembles with BOTH `-m i386` and `-m i386:x86-64` and calls a body
  fabricated if EITHER decode says so.
- **Small-constant cap.** A constant load counts only up to `0xff`, so a
  resolved link-time address (`mov $0x800123,%eax; ret`, the shape
  `rt_baremetal_heap_start` takes) is never mistaken for `return 0;`. This is
  the false-positive direction that got an earlier revision of the link-time
  guard rejected in
  `simpleos_fabricated_rt_guard_weak_real_false_positive_2026-07-28.md`.
- **Section-banner bug, found and fixed during development.** objdump prints
  `Disassembly of section .fini:` after the last symbol of a section. The first
  classifier counted that as an unknown mnemonic and flipped a genuine
  `xor %eax,%eax; ret` stub to REAL — a fail-open that depended on nothing but
  link order. Non-symbol lines now end the current symbol.
- **`--selftest`** builds fixtures and drives five cases every run; the PASS
  fixture additionally asserts the classifier actually SAW the stub, so it
  cannot pass for the wrong reason.

## Census (2026-08-09)

`build/simpleos_wm_fullscreen_evidence/simpleos_wm_production_desktop.elf`:

| | count |
|---|---|
| `rt_*` symbols in the kernel | 417 |
| with a constant-return body | 95 |
| — weak (`W`, fabricated by `auto_stubs.c`) | 50 |
| — strong (`T`, hand-written `return NIL_VALUE;`) | 45 |
| accounted with a written justification | 94 |
| **unaccounted** | **1 (`rt_index_of`)** |

The 94 are GPU/DMA/virtio "backend unavailable" seams (OpenCL, OpenGL, Vulkan,
CUDA, ROCm, oneAPI, Metal, host-GPU queue, ARM virtio-blk) plus a handful of
deliberate NOPs with written rationales in-tree (`rt_fb_blit32` / `rt_fb_fill32`
in `rt_extras.c`, `rt_font_glyph_index` at `baremetal_stubs.c:19668`,
`rt_pool_safepoint`, `rt_is_interpreter_runtime`). For all of those, nil IS the
intended answer. `rt_index_of` was the only one with text/collection semantics —
exactly the class where nil is never right.

**`rt_index_of` is deliberately left unaccounted.** The source fix landed at
`1f1c00aa578`; the ELFs currently in `build/` predate it, so the gate correctly
reports them as still carrying the defect. Once the WM kernel is rebuilt from
current source the symbol gets a real body and the gate goes green on its own.
Adding an accounting row instead would reinstate exactly the failure this
document describes.

## Arch asymmetry, recorded

Only x86_64 links `boot/auto_stubs.c`. aarch64 and riscv fail closed at the link
already, because nothing fabricates bodies for them — an unresolved `rt_*` is a
link error there. That asymmetry is why every accounting row is x86_64, and it
is recorded rather than removed: `auto_stubs.c` is what keeps the x86_64 boot
path linkable while the freestanding runtime is incomplete. It is not a licence.
This gate reads the ELF, so it polices any arch's kernel that grows a
constant-return body, fabricated or hand-written.

## Sabotage proof (both directions, run 2026-08-09)

| direction | command | verdict | exit |
|---|---|---|---|
| strong definition present | `--accounting <empty> --prefix rt_probe good.elf` | `PASS — 1 symbol(s) checked across 1 ELF(s), every constant-return body accounted for` | 0 |
| strong definition REMOVED, weak 0-stub binds | `--accounting <empty> --prefix rt_probe bad.elf` | `FAIL — 1 symbol(s) checked across 1 ELF(s), 1 finding(s)` | 1 |
| real kernel, committed accounting | `<wm kernel>.elf` | `FAIL — 417 symbol(s) checked across 1 ELF(s), 1 finding(s)` (names `rt_index_of`) | 1 |
| real kernel, post-fix simulation | `--accounting <+rt_index_of row> <wm kernel>.elf` | `PASS — 417 symbol(s) checked across 1 ELF(s), every constant-return body accounted for` | 0 |
| no artifact | `/nonexistent/kernel.elf` | `ERROR — nothing was checked (no ELF yielded a usable rt_* symbol set)` | 2 |
| built-in fixtures | `--selftest` | `PASS — 5 symbol(s) checked (selftest fixtures a-e)` | 0 |

## Usage

```sh
sh scripts/check/check-simpleos-fabricated-rt-elf.shs                 # scan default kernel paths
sh scripts/check/check-simpleos-fabricated-rt-elf.shs <kernel.elf>    # scan one artifact
sh scripts/check/check-simpleos-fabricated-rt-elf.shs --selftest      # fixtures only
```

Read the verdict line, which is always the last line of stdout.

## See also

- `doc/08_tracking/bug/text_index_of_returns_nil_in_simpleos_freestanding_2026-07-28.md`
- `doc/08_tracking/bug/simpleos_fabricated_rt_guard_weak_real_false_positive_2026-07-28.md`
- `doc/08_tracking/bug/bytespan_starts_with_dropped_from_kernel_closure_weak_nil_stub_2026-07-28.md`
- `test/01_unit/os/kernel/boot/baremetal_rt_index_of_not_fabricated_spec.spl`
