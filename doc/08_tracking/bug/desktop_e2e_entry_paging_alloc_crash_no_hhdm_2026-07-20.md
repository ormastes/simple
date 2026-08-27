# desktop_e2e_entry kernel crashes in paging _alloc_table_page during 4GB identity-map (no Limine HHDM)

- **ID:** desktop_e2e_entry_paging_alloc_crash_no_hhdm_2026-07-20
- **Status:** FIXED (2026-07-20 — see "Root cause + fix" below)
- **Severity:** medium (blocks the P1 framebuffer golden generator + SYS-GUI-006 spec path; main desktop entry unaffected)
- **Lane:** native-build (FIXED seed, cranelift, x86_64), QEMU q35

## Root cause + fix (2026-07-20)

**The crash was NOT an HHDM/virtual-address problem.** Disassembly of the
crashing ELF (sha256 863c6a3a..., guest rip=0x820ad9e) shows the ud2 is a
compiler-inserted **"runtime error: field access on nil receiver"** panic
inside `kernel__arch__x86_64__paging___alloc_table_page`, on the
`if val Some(f) = frame: ... f.pfn * PAGE_SIZE` shape — an instance of the
already-filed baremetal miscompile class
`baremetal_option_field_unwrap_faults_class_2026-07-18.md`
(Option-unwrap/if-val-then-field faults on the freestanding cranelift
x86_64-unknown-none lane). Two contributing defects:

1. **Duplicate symbol binding:** `desktop_e2e_entry` called
   `vmm_init(g_pmm, 0)`; `vmm_init` with an identical signature exists in
   BOTH `os.kernel.memory.vmm_core` (intended, raw-scalar alloc) and
   `os.kernel.arch.x86_64.paging` (Option<PageFrame> alloc). The call bound
   to the arch-paging copy. The production desktop entry
   (`gui_entry_desktop.spl`) boots clean because it calls the unambiguous
   `vmm_init_from_global_pmm(0)`.
2. **Miscompiled Option-of-struct in arch paging:** arch paging's
   `_alloc_table_page` used `pmm_alloc_page() -> PageFrame?`; the Some
   payload arrives nil-receiver on the baremetal native lane (filed class),
   so the second allocation (first `_ensure_table_entry` during the 4GB
   identity map) hit the panic trap. `hhdm_offset=0` is CORRECT on this
   lane (GRUB/multiboot identity-maps low memory; the first table page was
   successfully zero-filled at virt==phys before the panic).

**The `[BOOT] WARNING: No HHDM response from Limine` line is structural,
not causal:** this kernel is booted via OVMF+GRUB **multiboot**, so Limine
boot-protocol requests are never answered; the same warning appears in
successful `gui_entry_desktop` boots.

**Fix (both halves):**
- `desktop_e2e_entry.spl`: `vmm_init(g_pmm, 0)` →
  `vmm_init_from_global_pmm(0)` (same init as the production desktop).
- `arch/x86_64/paging.spl` `_alloc_table_page`: `pmm_alloc_page()`
  Option<PageFrame> → scalar `pmm_alloc_page_raw()` (the same per-site
  remedy the repo already applied in `vmm_core`; "scalar ABI owner used by
  freestanding bootstrap paths").

**Also required to even build desktop_e2e from clean origin/main** (the
original report was built from a working copy with pre-rv64-wave file
versions; clean origin/main could not build the kernel at all):
- `src/lib/.../baremetal/riscv/__init__.spl`: removed the ambiguous
  `TrapFrame` package export (plic.spl and startup.spl both define a
  different `struct TrapFrame`; no consumer imports it via the package).
- Cross-arch import leak: the seed's cfg strip does not strip @cfg-gated
  top-level `use` lines, so new rv64 imports in `user_entry_bridge.spl`,
  `memory/user_address_space.spl`, and `net/tls_shim.spl` pulled riscv64
  modules (RV64-only inline asm + a MIR-unlowerable deref store in
  `riscv64/interrupt.spl`) into every x86_64 kernel build. Fixed by moving
  those imports into their @cfg'd fn bodies (fn-local `use`; discovery
  strips wrong-arch fn variants before dep collection) and by replacing the
  whole-struct deref stores in `riscv64/interrupt.spl` with a field-wise
  `_rv64_ctx_store` (@repr(C) layout fixed by the RV64_CONTEXT_BYTES asm
  contract).

**Evidence (2026-07-20, OVMF pflash + grub-mkstandalone multiboot, q35,
2G, -vga std, QMP screendump — no `-kernel`, no isa-debug-exit):**
- Before (bug-session ELF, sha-verified 863c6a3a): serial reaches
  `[VMM] Identity-mapping first 4GB...` then exception frame
  rip=0x820ad9e, hang.
- After (fixed build, 5,084,496-byte ELF): `[VMM] Identity-mapped 4GB with
  2MB pages (2048 entries)` → `[desktop-e2e] memory-bootstrap:ok` →
  `shell-ready` → **`launcher-ready apps=15`** (the launcher now registers
  15 apps, not the 5 this doc originally anticipated) → `desktop-ready` →
  `paint-settle:done`; QMP screendump of the probe scene is 100% non-black
  (1024x768, 20 distinct colors, both mock windows + taskbar strips
  present). The remaining `TEST FAILED` at the very end of the run is the
  separate app-launch e2e stage (`/sys/apps/browser_demo` spawn fails with
  no VFS mounted) — out of scope for this paging bug.
- The spec baseline path mismatch noted below is also fixed
  (`test/baselines/...` → `test/09_baselines/...`).

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
