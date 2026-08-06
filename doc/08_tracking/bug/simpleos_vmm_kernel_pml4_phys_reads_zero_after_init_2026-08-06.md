# `vmm_kernel_pml4_phys()` reads 0 after a SUCCESSFUL vmm_init — blocks every FS-exec ring-3 spawn

- **ID:** simpleos-vmm-kernel-pml4-phys-reads-zero-2026-08-06
- **Status:** OPEN — root-cause investigation in progress
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
"cross-module global" story is not sufficient on its own — the read goes through
`vmm_core`'s own function. Candidate mechanisms still to discriminate:
duplicate `.bss` storage per object in the freestanding link; the accessor being
inlined into the caller's object against a different copy; the two init paths
writing different storage; or `g_vmm_initialized` and `_vmm_pml4_phys`
disagreeing.

This is worth root-causing rather than accepting: the SimpleOS freestanding
landmine catalog states that *scalar* module vars land in zeroed `.bss` and are
reliable (unlike array/`[text]` initializers, which genuinely do not run). A
scalar failing this way contradicts the documented contract.

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
