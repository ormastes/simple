# desktop_e2e_entry kernel crashes in paging _alloc_table_page during 4GB identity-map (no Limine HHDM)

- **ID:** desktop_e2e_entry_paging_alloc_crash_no_hhdm_2026-07-20
- **Status:** OPEN
- **Severity:** medium (blocks the P1 framebuffer golden generator + SYS-GUI-006 spec path; main desktop entry unaffected)
- **Lane:** native-build (FIXED seed, cranelift, x86_64), QEMU q35

## Symptom
`examples/09_embedded/simple_os/arch/x86_64/desktop_e2e_entry.spl` (the
generator for test/09_baselines/simpleos_desktop_framebuffer per its spec)
crashes deterministically during boot, before `[desktop-e2e]
launcher-ready apps=5`: compiler-inserted panic trap (`rt_eprintln_str` +
`ud2`) inside `kernel__arch__x86_64__paging___alloc_table_page`
(src/os/kernel/arch/x86_64/paging.spl) while "Identity-mapping first 4GB",
guest rip=0x820ad9e. Reproduced at 512M and 2G RAM, qemu64 and max CPU.
Two independent builds (warm + empty cache) → byte-identical ELF
(sha256 863c6a3a...), ruling out cache artifacts.

## Lead
Serial prints `[BOOT] WARNING: No HHDM response from Limine` immediately
before the fault — plausible root: missing HHDM offset → bad virtual
address in the page-table zero-fill loop. Not chased further (found during
a baseline-regen pass, out of its scope).

## Contrast
`gui_entry_desktop.spl` (the production desktop entry, same theme/font
stack, multiboot/GRUB boot path) boots clean to desktop-ready in the same
session — the defect is specific to the desktop_e2e_entry/Limine path.

## Also noted
test/system/simpleos_desktop_framebuffer_spec.spl hardcodes baseline path
`test/baselines/...` while the goldens live in `test/09_baselines/...` —
pre-existing path mismatch; the spec cannot currently run anyway
(test-daemon wall).

## Fix direction
Restore/handle the Limine HHDM response on this entry's boot path (or make
_alloc_table_page fail gracefully with a serial diagnostic when HHDM is
absent), fix the spec's baseline path, then regenerate the golden via its
own generator (see the baseline README for the exact recipe).
