# `vmm_kernel_pml4_phys()` reads 0 after a SUCCESSFUL vmm_init — blocks every FS-exec ring-3 spawn

- **ID:** simpleos-vmm-kernel-pml4-phys-reads-zero-2026-08-06
- **Status:** FIXED 2026-08-06 — verified by a positive in-guest marker (below)
- **Severity:** CRITICAL — blocks in-guest execution of BOTH the clang toolchain
  and the Simple compiler payload. Gates AC-4..AC-8 of the migration campaign.
- **Owner path:** `src/os/kernel/memory/vmm_core.spl`,
  `src/os/kernel/memory/vmm_address_space.spl`
- **Found by:** two independent lanes on the same day (the OVMF clang gate and
  the FS-exec fork/spawn lane), which is strong corroboration.

## Evidence — the write succeeds and the read returns zero

Booting `build/os/simpleos_ssh_ring3_uefi128.elf` under REAL OVMF pflash
(`scripts/os/scp_retrieve_over_ssh_uefi.shs`, KVM), the serial
(`build/os/scp_retrieve_over_ssh_uefi.serial.log`) shows VMM init running to
completion:

```
[VMM] Initializing virtual memory manager...
[VMM] PML4 at physical 0x<nonzero>
[VMM] Identity-mapping first 4GB...
[VMM] Identity-mapped 4GB with 2MB pages (N entries)
[VMM] VMM initialization complete
```

Later, on the FS-exec ring-3 spawn of the 127 MB clang image:

```
[fs-exec] path-resolve clang -> /usr/bin/clang
[fs-exec] heap:stream-open-ok path=/usr/bin/clang len=127572072 hdr_prefix=456
[spawn] stream+heap path=/usr/bin/clang hdr_len=456 file_len=127572072
[spawn] parsed entry=0x1073741824          <-- 0x40000000, CORRECT
[VMM] create_user_address_space: VMM not initialized — legacy AS=1
[spawn] FAIL user-AS synthetic root=1
[sshd] ring3 deferred heap-stream spawn returned rc=-1; accept loop continues
```

Everything up to the address space is correct: the binary is resolved, opened,
its ELF header parsed, and the entry point read as exactly the ring-3 link base.
The failure is solely that the guard `if vmm_kernel_pml4_phys() == 0:`
(`vmm_address_space.spl:75`, also `:91`, `:119`) sees **zero** for a PML4 the
serial already reported as a nonzero physical address.

## Code shape

- `vmm_core.spl:177` — `var _vmm_pml4_phys: u64 = 0` (module-level scalar)
- `vmm_core.spl:294`, `:325` — the two vmm_init paths that assign it
- `vmm_core.spl:191-192` — `fn vmm_kernel_pml4_phys() -> u64: _vmm_pml4_phys`
- `vmm_address_space.spl:14` — imports the accessor from `vmm_core`

Note the accessor lives in the SAME module as the global, so a naive
"cross-module global" story was never sufficient — the read goes through
`vmm_core`'s own function.

## ROOT CAUSE — two parallel VMM implementations printing IDENTICAL banners

Not a codegen bug. A **wiring** bug, and the reason it burned a day across two
lanes is that the decoy was the evidence itself.

- `nm` finds exactly ONE `_vmm_pml4_phys`
  (`src__os__kernel__memory__vmm_core___vmm_pml4_phys`) → duplicate-`.bss`
  ruled out.
- `objdump` of `vmm_kernel_pml4_phys` shows a real body
  (`mov $0x80c4138,%rdi; mov (%rdi),%rax; ret`) → not a fabricated stub. The
  global genuinely held 0.
- The only `vmm_init` in the linked ELF is
  `src__os__kernel__arch__x86_64__paging__vmm_init`. **`vmm_core.spl`'s own
  `vmm_init` / `vmm_init_from_global_pmm` (`:273`, `:282`) have ZERO callers
  repo-wide — dead code.**

The live initializer is `src/os/kernel/arch/x86_64/paging.spl:214` (via
`X86Paging.init`). It stores the root in **its own** `g_vmm.pml4_phys`
(`paging.spl:230`). Everything downstream — `create_user_address_space`,
`vmm_clone_kernel_low_private`, `vmm_copy` — reads
`vmm_core::vmm_kernel_pml4_phys()`, which **nothing ever wrote**.

**Both implementations print byte-identical `[VMM] …` banners.** So the serial
"proof" that init succeeded was emitted by the OTHER init. Reading a log for a
success marker cannot distinguish two implementations that log the same words —
the marker must identify its writer.

## Fix (kernel-source layer)

New `vmm_publish_kernel_pml4(pml4_phys, hhdm_offset)` in `vmm_core.spl` sets the
three **scalars** (`_vmm_pml4_phys`, `_vmm_hhdm_offset`, `g_vmm_initialized`)
and prints a marker naming itself; `paging.spl`'s `vmm_init` calls it with its
LOCAL live values. Scalars only — `g_vmm` is a struct global with a constructor
initializer, the unreliable freestanding category. +35 lines across two files.

## Verification — positive marker, plus anti-fabrication ratchet

```
  [ok]   L1 OVMF -> GRUB-EFI app ran
  [ok]   L2 multiboot handoff -> kernel _start
  [ok]   L3 sshd ring-3 accept loop (payload overlap fault cleared)
  [ok]   L4 in-guest clang compiled /hello.o under OVMF
[VMM] portable VMM published kernel PML4 0x402718720
[spawn] parsed entry=0x1073741824
[oo-nvme] persist /hello.o -> OK
[syscall] exit status=0
```
(`build/os/vmm_gate_run.log`, 2026-08-06 05:48; serial
`build/os/scp_retrieve_over_ssh_uefi.serial.log`.)

Acceptance was deliberately a POSITIVE marker (`persist /hello.o -> OK`), never
the absence of the failure line — an absence condition is also satisfied by a
stubbed-out accessor. The `portable VMM published` line is itself
anti-fabrication proof: a weak no-op stub prints nothing. Failure markers
`VMM not initialized` / `FAIL user-AS` / `rc=-1` all occur **0** times.

Stub ratchet: the entry was baselined on the PRE-fix build (56 rows, now in
`config/freestanding_fabricated_stub_baseline.sdn`), and the post-fix build
reports **56 known, 0 new** — so the fix introduced no fabricated symbols. Any
future fabrication in this entry now fails the build instead of shipping a
no-op.

## Still open

- **L5** host-side `getfile` retrieval returns an empty object. The serial ends
  healthy (`exit status=0`, object base64 present, no fault), so this is the
  retrieval transport, not the VMM/ring-3 path.
- **Follow-up:** the two VMM implementations with identical banners should be
  consolidated. Leaving both is exactly what made this defect cost two lanes a
  day; merging was out of scope for the fix.

## Do NOT "fix" it by relaxing the guard

The guard protects against handing a null PML4 to user address-space
construction. Making `create_user_address_space` proceed anyway converts a clean
`rc=-1` into a page fault later, at a point far from the cause.

## Related

- `doc/08_tracking/bug/fs_exec_ring3_fork_unreachable_spawnwait_2026-08-06.md` —
  the parallel lane's write-up; it also establishes that fork is *unreachable*
  (not broken) on the FS-exec path because such processes are never scheduler
  Tasks, and adds a `SpawnWait` primitive that is blocked by this same defect.
- `doc/07_guide/os/baremetal_simple_codegen_landmines.md` — freestanding
  codegen landmine catalog.

## Correction to the record

The gate commit `269cd178151` attributed an earlier failure of this gate to the
hardcoded 120 s compile budget, describing the guest as "still streaming when
the budget expired". The serial shows otherwise: the spawn had already failed
with `[spawn] FAIL user-AS` and returned to the sshd accept loop. The KVM
selection and the `CLANG_WAIT` budget in that commit are still correct and
useful changes — KVM is what made the run reach the spawn failure quickly enough
to diagnose — but the root cause named there is wrong, and it is this defect.
The gate's failure-message chain now tests for the spawn/VMM failure FIRST and
prints "this is NOT a timeout, do not raise CLANG_WAIT", so the next reader is
not sent down the same path.
