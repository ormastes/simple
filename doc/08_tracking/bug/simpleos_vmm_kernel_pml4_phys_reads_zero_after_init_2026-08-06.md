# `vmm_kernel_pml4_phys()` reads 0 after a SUCCESSFUL vmm_init — blocks every FS-exec ring-3 spawn

- **ID:** simpleos-vmm-kernel-pml4-phys-reads-zero-2026-08-06
- **Status:** FIXED 2026-08-06 — verified by a positive in-guest marker (below);
  **re-confirmed 2026-08-08 by re-reading 4 independent 2026-08-06 post-fix
  serial logs** (not a fresh live run — see 2026-08-08 section), each bearing
  the anti-fabrication `[VMM] portable VMM published kernel PML4 ...` marker
  followed by `[spawn] user AS ready (private low) root=...`: general FS-exec
  ring-3 spawn no longer returns `rc=-1`. The narrower Lane-B3 `SpawnWait`
  harness is separately blocked: its entry `.spl` file was never committed to
  `HEAD`'s history (confirmed via `git cat-file -e HEAD:<path>` /
  `git rev-list -1 HEAD -- <path>`, both empty) — a build-system gap, not a
  VMM/PML4 recurrence — see 2026-08-08 section below.
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

## Interpreter-level regression spec added 2026-08-07

`test/01_unit/os/kernel/memory/vmm_publish_kernel_pml4_spec.spl` exercises the
`vmm_publish_kernel_pml4` / `vmm_kernel_pml4_phys` store-load pair directly
(interpreter level, no QEMU needed): publish a known PML4 root, assert the
accessor reads back the exact value; publish a second value and assert it is
reflected (rules out a cached/stale read); and a dedicated
"never reads back zero after a nonzero publish" assertion for the exact
regression shape. `bin/simple test` on this file: `Results: 3 total, 3 passed,
0 failed`.

Sabotage check performed: commenting out `_vmm_pml4_phys = pml4_phys` in
`vmm_core.spl:294` (leaving `_vmm_hhdm_offset` / `g_vmm_initialized` writes
intact) reproduces the exact defect and turns all 3 examples red
(`Results: 3 total, 0 passed, 3 failed`, `expected 0 to equal ...`). Restoring
the line returns the file to a clean diff and 3/3 green — confirms the spec
is load-bearing, not vacuous.

## Still open

- **L5 correction 2026-08-07 — not reproducing as of source clean vs HEAD:**
  the "empty object" observation above predates two later runs of the exact
  same gate, both on source that is clean vs the current HEAD for every file
  in the chain (`ssh_session.spl`, `baremetal_stubs.c`,
  `scp_retrieve_over_ssh_uefi.shs` — verified via `git status --porcelain` /
  `git log`): `build/os/l5_fix_run.log` (2026-08-06 06:01,
  `retrieved_uefi.o size=712`) and the matched pair
  `build/os/l5_printing_hello.log` + `build/os/scp_retrieve_over_ssh_uefi.serial.log`
  (both 2026-08-06 06:03) — guest and host agree in that run: serial shows
  `[sshd-session] getfile path=/hello.o fsize=1000 bytes=1000`, host shows
  `retrieved_uefi.o size=1000`, `Machine: EM_X86_64`, host exit code `7` (the
  expected `a.out` return value), and the script prints
  `PASS: clang-over-SSH-under-OVMF VERIFIED`. `baremetal_stubs.c` picked up two
  further unrelated fixes after these runs (`7dd587ba2f5` at 06:14,
  `c3f5d82c9f1` at 08:41, the latter removing a 1 MiB guest-`open()`
  truncation) — neither reintroduces this symptom.
  **Do not write "FIXED"** — no commit is attributable to a fix; the
  reproduction the "Still open" note was based on (05:48) may have been a
  transient/timing condition, and the correct confirming action going forward
  is a fresh run of `sh scripts/os/scp_retrieve_over_ssh_uefi.shs`, expecting
  the same markers (`retrieved_uefi.o size=<nonzero>`, `Machine: EM_X86_64`,
  `retrieved.o host exit code = 7`, `PASS: ...VERIFIED`).
  - **Chain traced** (for the next reader): SSH `getfile <path>` command →
    `ssh_session.spl:923` (`0x67` byte match) →
    `_scp_read_file_bytes` (`ssh_session.spl:235`) →
    `simpleos_fat32_stream_open` / `simpleos_fat32_stream_read_at`
    (`baremetal_stubs.c:2917`, `:2965`) — synchronous, unbuffered,
    per-sector NVMe reads. Write side: ring-0 syscall-exit handler
    `_bare_dump_all_outputs` (`baremetal_stubs.c:16762`) →
    `fat32_write_file` (`baremetal_stubs.c:3157`) →
    `_fat32_write_cluster` / `_fat32_write_fat_entry`
    (`baremetal_stubs.c:2527`, `:2561`) → `_nvme_write_sector_impl`
    (`baremetal_stubs.c:2096`) — also synchronous, unbuffered, one NVMe I/O
    command per 512-byte sector, no write-back cache to flush. **This chain is
    entirely separate from the newer Simple-native FAT32 layer**
    (`src/os/kernel/fs/fat32.spl` / `fat32_fd_table.spl`,
    `Fat32Filesystem.rename_at`) — that layer has zero callers in this getfile
    path, so the "mount-accessor persistence wall" flush hypothesis for that
    layer does not apply here; there is no dirty-cluster cache in the chain
    above to flush, which is consistent with the retrieval already succeeding.
  - **Real residual bound found while tracing (not yet hit by /hello.o):**
    `_scp_read_file_bytes` (`ssh_session.spl:237`) hard-fails
    (`return ([], -1)`) whenever `fsize > 4194304` (4 MiB), and the getfile
    dispatcher (`ssh_session.spl:928`) turns any `fsize <= 0` into an exit-1
    response with **zero bytes** — a genuine empty host-side retrieval,
    exactly the L5 symptom, for any file over 4 MiB. `/hello.o` (712–1000
    bytes) never exercises this. The next artifact this campaign retrieves
    (e.g. `/hello.elf`, a linked output) should be checked against this bound
    before assuming L5 is fully closed.
  - **Spec step skipped, and why:** the getfile chain is freestanding C behind
    `@cfg(x86_64)` `extern fn` declarations (`simpleos_fat32_stream_open`,
    `simpleos_fat32_stream_read_at`) with no in-process/interpreter path —
    there is nothing to construct without booting real (or QEMU) hardware. A
    spec against `fat32_fd_table.spl` / `Fat32Filesystem` would test a layer
    this trace shows is not part of the getfile chain, so none was added.
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

## Re-check 2026-08-08 — PML4 fix IS effective; general FS-exec ring-3 spawn now succeeds; the SpawnWait (Lane B3) harness is separately blocked by a missing source file

Triggered by project memory still listing "every FS-exec ring-3 spawn returns
`rc=-1`" as **THE blocker**, despite the 2026-08-07 spec addition. Re-checked
whether that claim is still true.

**Verdict: the PML4 fix is effective and general ring-3 spawn is UNBLOCKED.**
Evidence — four independent POST-fix serial logs (all after commit
`4575b4ce88d`, 2026-08-06 05:52:34, which added
`vmm_publish_kernel_pml4`/`paging.spl:239`), spanning 2026-08-06 06:11 through
13:56:

- `build/os/ssh_lld_link_uefi.serial.log:60` — `[VMM] portable VMM published
  kernel PML4 0x402718720`, then `:707` `[spawn] user AS ready (private low)
  root=402755584`, PT_LOAD mapped, stack/heap mapped. **No `FAIL user-AS`, no
  `rc=-1`.**
- `build/os/scp_retrieve_over_ssh_uefi.serial.log:714` — same pattern, spawning
  `/usr/bin/clang` (127 MB image, the exact scenario in the original evidence
  block above).
- `build/os/ssh_b1_witness_uefi.serial.log:755` — same pattern.
- `build/os/ssh_simple_hello_uefi.serial.log:585-593` — same pattern, spawning
  `/usr/bin/simple`; the spawned process reaches `[spawn] entering user cs=0x2b
  ... rip=0x1073741824`, then genuinely runs in ring 3 (`open path=/hello.spl`,
  `NVMe read 39 bytes`, `phase=post-read cs=0x2b cpl=3`) before faulting later
  (see below) — this is a downstream, unrelated bug, not the PML4/spawn-setup
  defect.

`/usr/bin/grep -c rc=-1` is 0 in every one of these four logs, but that is a
secondary check, not the proof — the load-bearing evidence is the POSITIVE
`portable VMM published kernel PML4` marker itself (the doc's own
anti-fabrication design: a stubbed accessor prints nothing), confirmed
single-boot in the checked log
(`/usr/bin/grep -c 'BdsDxe: starting Boot0001' ssh_simple_hello_uefi.serial.log`
= 1, ruling out the marker and the success line coming from two different
boots concatenated in one file). The guard at `vmm_address_space.spl:75/:91/:119`
is passing in all four logs. **The headline finding from the memory note is
stale**: this specific defect was fixed and general FS-exec ring-3 spawn (the
clang/lld/simple-interpreter payloads) has not returned `rc=-1` on the general
path since — as of the 2026-08-06 logs re-read on 2026-08-08; not re-run live
today (see budget note below).

**However, one specific harness regressed independently and is currently
unbuildable — not for a VMM reason.** `scripts/os/build_spawn_wait_ring3.shs`
(Lane B3, the `SpawnWait`/syscall-120 nested-spawn primitive; see
`doc/08_tracking/bug/fs_exec_ring3_fork_unreachable_spawnwait_2026-08-06.md`)
references entry file
`examples/09_embedded/simple_os/arch/x86_64/fs_exec_spawn_wait_ring3_entry.spl`.
That file **does not exist on disk** (`git status --porcelain` shows the build
script `A`dded but not this entry file; `find` over the whole tree finds no
file by this name anywhere). A live rebuild attempt today
(`SKIP_PAYLOAD=1 BOOT_WAIT=60 timeout 500 sh scripts/os/build_spawn_wait_ring3.shs`)
failed immediately at the kernel-build step:
`Build failed: failed to read .../fs_exec_spawn_wait_ring3_entry.spl: No such
file or directory (os error 2)` — never reached QEMU. The stale
`build/os/spawn_wait_ring3.serial.log` (mtime 2026-08-06 05:31:15, **21 minutes
before** the 05:52:34 fix commit) still shows the old `FAIL user-AS
... rc=-1` failure — that is pre-fix evidence, not current status; it should
not be read as still-reproducing.

**Recoverability checked and ruled out via git — not just inferred:**
`git cat-file -e HEAD:<path>` fails ("does not exist in 'HEAD'"), and
`git rev-list -1 HEAD -- <path>` returns nothing, i.e. **no commit reachable
from HEAD ever touched this path** — it was never committed, not deleted in a
later commit. (`jj file show <path>` could not be used to cross-check further:
the jj workspace itself is stale — "not updated since operation
f1204fdea46d" — a separate, already-known issue, not investigated here.) So
this is not a small "restore a lost commit" fix; the file must be
reconstructed from scratch (the 2026-08-06 write-up documents its role and the
harness reaching D6 with it in place that day, so its intended content is
known, but recreating and re-verifying it is a real implementation task, not a
one-line recovery — left out of scope for this investigation per the "no large
kernel fix" instruction).

**Board-runnable check:** `build_spawn_wait_ring3.shs` uses OVMF pflash
(`OVMF_CODE_4M.fd`/`OVMF_VARS_4M.fd`) and explicitly documents "NEVER
`-kernel`" per the board-runnable rule; no `-kernel` usage found in the script
itself. **But the C source it links against, `baremetal_stubs.c`, still has
several unconditional `outb(0xF4, ...)` ("isa-debug-exit") calls on ring-3
exit paths** (e.g. `:16917`, `:17553`, plus two bare `for(;;) outb(0xF4, 0)`
loops at `:647`/`:700`), including the `_bare_exec_handle` case-0
`exit(status)` path the B3 lane's own doc names as the halt-on-exit hazard.
This is a *documented*, not silent, gap — the code has adjacent comments
acknowledging it (`:14904-14906` "If isa-debug-exit is not present the write
is ignored"; `:16749-16753` "also not board-runnable — isa-debug-exit does not
exist outside QEMU's ISA bus"; `:17419-17420` shows the intended pattern, QEMU
`outb` then a board-safe `for(;;) cli;hlt` fallback) — but not every site
below those comments has that fallback, so on real hardware a ring-3
`exit(status)` write to port 0xF4 is a harmless no-op (unmapped I/O port,
silently dropped) rather than a crash, yet the process does not cleanly signal
its exit status to anything watching the board the way QEMU's isa-debug-exit
does. Flagging per the board-runnable rule rather than fixing — it predates
this investigation and is not part of the PML4/spawn defect.

**New, separate downstream finding (not this bug):** in
`ssh_simple_hello_uefi.serial.log`, after ring-3 spawn fully succeeds and the
spawned `/usr/bin/simple` interpreter opens and reads `/hello.spl` (39 bytes),
it hits a ring-3 page fault: `errcode=0x...5` (present, ring3-cpl, non-write —
protection violation), `cs=0x2b` (still ring 3), `cr2=0x0` (faulting address
NULL). This looks like a null-pointer dereference inside the spawned `simple`
interpreter after the file read, unrelated to VMM/PML4/spawn setup. Not
investigated further here — flagging for whoever picks up the in-guest
`simple`-interpreter lane next.

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
