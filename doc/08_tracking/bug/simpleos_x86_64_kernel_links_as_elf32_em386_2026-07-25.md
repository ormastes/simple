# SimpleOS x86_64 WM kernel links as ELF32/EM_386 despite an x86_64 target — newly-added ELF gate now rejects it

- **ID:** simpleos_x86_64_kernel_links_as_elf32_em386_2026-07-25
- **Status:** RESOLVED — admission now validates the post-wrap Multiboot1 ELF32/EM_386 contract
- **Severity:** high — blocks the `SimpleOS-WM × QEMU` showcase-matrix cell
- **Resolution:** validate the post-wrap image as ELF32/EM_386; retain
  ELF64/EM_X86_64 expectations for compiler objects and pre-wrap artifacts.
  Preserve the artifact path across byte-field parsing so the machine check
  does not interpret the already-parsed ELF class byte as a filename.

## Measurement

Kernel built with the harness's exact command
(`scripts/check/check-simpleos-wm-fullscreen-evidence.shs:~510-520`), output
preserved instead of the harness's `rm -f` on failure:

```
Build complete: 5 compiled, 657 cached, 0 failed
Linked (freestanding): kernel_probe.elf (9281 KB) via clang --target=x86_64-unknown-elf
```

ELF header of that artifact:

| field | actual | required by gate |
|---|---|---|
| magic | `7f454c46` | `7f454c46` ✓ |
| class | **1 (ELF32)** | 2 (ELF64) ✗ |
| data | 1 (LE) | 1 ✓ |
| machine | **3 (EM_386)** | 62 (EM_X86_64) ✗ |

## The anomaly

Every input to this build says x86_64:

- entry `examples/09_embedded/simple_os/arch/x86_64/gui_entry_desktop.spl`
- linker script `examples/09_embedded/simple_os/arch/x86_64/linker.ld`
- `--target x86_64-unknown-none`, `--cpu x86-64-v1`
- link line: `clang --target=x86_64-unknown-elf`

…yet the output is 32-bit i386. `linker.ld` contains **no** `OUTPUT_FORMAT` or
`OUTPUT_ARCH` directive (0 matches), so it is not overriding the format there.
It does declare `ENTRY(_entry32)` — a 32-bit entry symbol is normal for a kernel
that boots in protected mode and switches to long mode, but that alone should not
change the ELF class/machine of the linked image.

## Timeline — the gate is new, the ELF32 output is not

`elf_file_status`'s ELF64/`machine=62` assertions
(`check-simpleos-wm-fullscreen-evidence.shs:190-208`) **did not exist** in the
harness at either 2026-07-19 or 2026-07-23 (`grep -c 'invalid-elf-machine'` = 0
at both). It was added 2026-07-25.

The kernel, meanwhile, has been ELF32 the whole time: the on-disk
`build/simpleos_wm_fullscreen_evidence/simpleos_wm_production_desktop.elf` from
**Jul 22** is also class=1 / machine=3.

So the matrix report's "last PASS 07-18/19" predates the check. The cell did not
regress into ELF32 — **a new gate surfaced a pre-existing condition.**

## RESOLVED: the ELF32 output is INTENTIONAL — the new gate is wrong

An earlier draft of this file concluded "the check is probably right, do not
relax it." **That was wrong**, and is corrected here so nobody chases a
non-existent codegen bug.

Evidence:

1. **Input objects are ELF64/x86_64.** Sampled `.o` files under
   `build/simpleos_wm_fullscreen_evidence/native-cache` are all `class=2
   machine=62`. Codegen is correct; only the final image is 32-bit.
2. **The harness itself documents the downgrade as a deliberate step.**
   In `check-simpleos-wm-fullscreen-evidence.shs`, grep **`ELF32 wrap step`**:
   *"plus an llvm-objcopy on PATH for the ELF32 wrap step"* — with the
   `llvm-objcopy` discovery immediately following.
3. **The boot path requires it.** GRUB loads the kernel with
   `multiboot /boot/kernel.elf` and `insmod multiboot`.
   **Multiboot1 mandates a 32-bit ELF.** The 64-bit handoff happens after, at the
   `[BOOT64] call _start` marker — which the harness itself greps for as a
   success signal.

> **Cite by marker, not line number.** An earlier revision of this doc gave line
> numbers (499 / 638 / 648 / 758, `elf_file_status` at 190-208). Adding the
> in-code warning comment shifted everything below line 190 by ~20 lines and
> invalidated all of them in one edit. Current values, already stale-prone:
> `elf_file_status` ~210, ELF32 wrap ~519, multiboot ~658/668, BOOT64 ~778.

So the pipeline is: compile x86_64 objects → link → **objcopy-wrap to
ELF32/EM_386 for multiboot** → GRUB loads it → kernel switches to long mode.
An `EM_X86_64` assertion on the multiboot image contradicts the design.

### Correct fix

`elf_file_status` (`check-simpleos-wm-fullscreen-evidence.shs:190-208`) must not
demand class=2/machine=62 for the **multiboot** kernel image. Either:
- assert ELF32/EM_386 for the wrapped image (matching multiboot1), or
- run the ELF64 assertion against the **pre-wrap** linked artifact and a separate
  ELF32 assertion against the post-objcopy image.

This is not "relaxing a gate to go green": the gate encodes an expectation the
boot path cannot satisfy. It was added 2026-07-25 (absent at 07-19 and 07-23),
after the cell's last PASS, and asserts the wrong architecture for this stage.
Whoever added it should confirm the intent before it is changed.

## Prior blocker (resolved, for context)

This cell previously failed earlier in the pipeline with
`hir: cannot infer field type … struct 'ANY' field 'left_just_pressed'`
(duplicate `MouseEvent` types). Fixed in `a163f3977a2`; the kernel now compiles
662 files with 0 failures and links. The ELF format gate is the *next* blocker,
not a recurrence.
