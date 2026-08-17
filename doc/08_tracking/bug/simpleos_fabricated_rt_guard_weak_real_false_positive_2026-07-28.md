# Fabricated-`rt_*` link guard misclassifies weak-but-real definitions — blocks landing

- **Status:** FIXED
- Status re-verified 2026-08-17 by source inspection (independent
  re-verification pass). Both halves of the record are resolved:
  1. *No longer uncommitted.* The guard is committed and tracked —
     `git log -1 -- src/compiler/70.backend/backend/llvm_native_link.spl` =
     `e14a2ffb4df` ("fix(backend,mir): three fail-open sites made fail-closed"),
     and `git show HEAD:...llvm_native_link.spl` contains
     `simpleos_defined_symbols_any_binding` (5 occurrences). Working tree is
     clean against HEAD for that file.
  2. *The weak-vs-real false positive is gone.* The guard no longer classifies
     via `extract_symbols_nm` (which drops `W/w/V/v` at
     `backend/llvm_backend_tools.spl:42`). It uses the dedicated
     `simpleos_defined_symbols_any_binding`
     (`src/compiler/70.backend/backend/llvm_native_link.spl:1850-1880`), whose
     docstring cites this bug by filename and states the rule explicitly:
     weak definitions are INCLUDED, only `U`/`u` are skipped, and the actual
     fabricated/real classifier is the disassembled BODY check
     (`simpleos_trivial_body_rt_symbols`). It also records why
     `extract_symbols_nm` was deliberately not widened (it is exported at
     `backend/__init__.spl:174,182` and its weak-dropping is load-bearing for
     `llvm_backend.spl` codegen symbol tables).

  So the six real weak implementations named in this record (`rt_memcpy`,
  `rt_memset`, `rt_dma_alloc`, `rt_dma_phys_of`, `rt_dma_virt_of`,
  `rt_file_read_bytes` in `baremetal_stubs.c`) are now visible to the guard as
  defined and can only be flagged on body evidence.

  **Verified by source inspection only** — no SimpleOS x86_64 link was
  executed, so the "guard passes on the real production link" claim is not
  re-established by this pass.
- **Severity:** BLOCKER (would break every SimpleOS x86_64 production link)
- **Area:** `src/compiler/70.backend/backend/llvm_native_link.spl`
  (`simpleos_check_no_fabricated_rt_stubs`, ~`:1950`)
- **Filed:** 2026-07-28

## Context

SimpleOS freestanding links have a fail-open defect class: `auto_stubs.c`
fabricates ~4023 **weak** `rt_*` definitions returning `NIL_VALUE`, so an
unimplemented runtime symbol links clean and only corrupts data at runtime. This
shipped a real bug — `rt_array_copy` returned nil in the guest, silently
shredding every array copy. A link-time guard was written to catch the class.
The guard is correct in intent and its design notes are unusually careful
(it deliberately refuses a `rt_simd_` prefix allowlist so that
`rt_engine2d_simd_*` blitters cannot be swallowed). It nevertheless cannot land
in its current form.

## Defect

`simpleos_check_no_fabricated_rt_stubs` builds its set of "real" definitions with
`extract_symbols_nm` (`src/compiler/70.backend/backend/llvm_backend_tools.spl:42`).
That helper **explicitly skips weak symbols**:

    # Skip undefined and weak symbols
    if type_code == "W" or type_code == "w": continue
    if type_code == "V" or type_code == "v": continue

Therefore a symbol that is **weak but has a real body** can never enter the
`real` set. Channel 1 then classifies it as fabricated, because "referenced and
not in `real`" is precisely its fabrication test.

**Weak linkage does not imply fabricated.** `examples/09_embedded/simple_os/arch/x86_64/boot/baremetal_stubs.c`
defines real implementations with `__attribute__((weak))`, e.g. at lines
17726 / 17737 / 17745 / 17784: `rt_dma_alloc`, `rt_dma_bytes_to_array`,
`rt_dma_phys_of`, `rt_memset`, plus `rt_memcpy`.

## Evidence

Measured against the exact entry the baseline was derived from,
`build/simpleos_wm_fullscreen_evidence/simpleos_wm_production_desktop.elf`, with
its real user objects in `native-objects-uSdrJr/` (679 objects):

- 699 distinct undefined `rt_*` referenced by the user objects.
- All five weak-real symbols above are in that undefined set — so they reach
  Channel 1's test.
- Disassembly confirms real bodies (frame setup, argument spills, loops, real
  work) — none is a constant-return stub.
- Of the 60 weak `rt_*` bound into the final ELF, 7 survive the allowlist, and
  5 of those are exactly the weak-real symbols; none is in the baseline.
- Estimated Channel-1 fabricated set for this entry: ~272 symbols, of which
  **~271 are not in the 5-row baseline**.

The baseline `config/simpleos_fabricated_rt_baseline.sdn` contains 5 rows, all
for `simpleos_wm_production_desktop.elf`. A missing entry means an **empty**
baseline (maximum strictness). So the guard **refuses the link on the very entry
it was measured against**, and on every other entry as well.

## Root cause of the mismatch

The baseline's documented regeneration procedure and the implementation disagree
about weak symbols. The procedure computes "`rt_*` not defined by
crt0/baremetal_stubs/type_stubs/module_init" using plain `nm`, which **shows**
weak definitions — correctly excluding the weak-real ones and yielding 5 rows.
The implementation uses `extract_symbols_nm`, which **drops** them. The 5-row
baseline was therefore measured under semantics the code does not enforce.

The baseline file says so itself: *"!! INCOMPLETE — MUST BE POPULATED BEFORE THIS
GUARD LANDS !!"*, noting 101 entry points / 186 correctness-class symbols and
that landing as-is "fails every unmeasured entry on its first link".

## Required fix (do NOT weaken the gate)

1. Give the guard its own definition scan that **includes** weak symbols with
   non-trivial bodies, instead of reusing `extract_symbols_nm`. Weakness must not
   be the classifier; the existing body-level predicate
   (`simpleos_trivial_body_rt_symbols`) already encodes the right test —
   classify by disassembled body, never by binding or by name prefix.
2. Re-measure the baseline per entry under the corrected semantics.
3. Only then land, and only then add the riscv32/riscv64 call sites.

Do not disable the check, and do not paper over this by bulk-adding the ~271
symbols to the baseline — the baseline is shrink-only and records pre-existing
debt, never new debt.

## arm64 is a different, less dangerous failure mode

`link_simpleos_arm64` links **no `auto_stubs.c`** — only `crt0.S` plus
`baremetal_stubs.c` (verified: `auto_stubs.c` is compiled only on the x86_64
path, `llvm_native_link.spl:2179`). The arm64 `baremetal_stubs.c` carries several
hundred hand-written `rt_*` bodies.

Consequently arm64 has **no weak nil-stub channel at all**. An unimplemented
`rt_*` there — including `rt_array_copy` — is simply undefined at link time and
**fails the link loudly**. That is a materially different and much safer failure
mode than x86_64's silent nil binding, and it should not be described as the same
defect. The reported audit figures for `arm64/os_entry` are 397 undefined `rt_*`,
188 satisfied by hand-written bodies and 209 by nothing at all; those specific
counts were **not independently reproduced here** (no arm64 `os_entry` build
artifact is present in `build/`) and are recorded as reported.

Note that the arm64 guard call site (`:2088`) shares the same false-positive
mechanism if `baremetal_stubs.c` there also uses `__attribute__((weak))` on real
bodies — this was not measured.

## Related

- `doc/08_tracking/bug/simpleos_riscv64_defsym_unknown_symbol_aliasing_2026-07-28.md`
