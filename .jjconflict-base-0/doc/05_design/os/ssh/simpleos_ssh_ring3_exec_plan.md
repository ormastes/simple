# SimpleOS — "hello world over SSH" (ring-3 filesystem-exec): execution plan

Status: 2026-07-08. Goal: **`ssh guest <cmd>` executes an on-disk clang-built ELF
in ring-3 over a real SSH connection** (one-shot demo: the program exits and takes
QEMU down; success is proven on the serial log — `hello from clang on simpleos` +
`[user] exit rc=42`).

The OS-side execution path is **DONE and verified** (see
`scripts/os/build_clang_hello_ring3.shs`, memory
`project_simpleos_clang_hello_fs_ring3`). The SSH transport around it is largely
built and de-risked. **One blocker remains, and it is now root-caused to a core
compiler/runtime ABI bug** (not a sshd bug) — see "Critical path" below.

## Progress ledger (2026-07-08)

| Piece | State | Evidence |
|-------|-------|----------|
| Clang ELF runs from FS in ring-3 → clean exit | **DONE** | `build_clang_hello_ring3.shs` self-test PASS; serial `hello from clang on simpleos` + `[user] exit rc=42` |
| PML4[0]-safe loader mapping | **DONE** | commit `b376cb7d`; clang links at 0x10000000 |
| EFER.NXE / crt0 `environ` / native `exit` syscall | **DONE** | commit `afbecf11` |
| M1.5 post-vmm FAT read (`vmm_map_nvme_bar_high` after `vmm_init`) | **DONE** | commit `fbe6969a`; post-vmm `read size=13888` → hello → exit 42 |
| Merged ring-3 + sshd kernel builds | **DONE** | `ssh_ring3_entry.spl`, `build/os/simpleos_ssh_ring3.elf` 22 MB, 0 failed (commit `6f8a3af9`) |
| Merged kernel boots, sshd listens AFTER `vmm_init` | **DONE** | serial `pmm+vmm online (+nvme bar high)` → `[sshd] accept loop start` |
| virtio-net (PIO) survives `vmm_init` | **DONE** | sshd accept loop + TCP connect work post-vmm; no `vmm_map_virtio_net_bar_high` needed |
| Real host SSH client connects, TCP + version banner | **DONE** | `[tcp] Connection established`, `[sshd] accepted client`, banner sent, client version `SSH-2.0-OpenSSH_9.6p1` received |
| **x64 SSH LOGIN completes (version → KEX → auth)** | **BLOCKED** | version exchange fails; root-caused to a C↔Simple `RuntimeValue`/`[u8]` ABI mismatch (below) |
| SSH exec dispatch → `fs_exec_spawn_ring3` | **not started** | small; gated on login |
| One-shot demo harness | **not started** | small; gated on login |
| Interactive shell / return-to-scheduler | **deferred (LARGE)** | not required for one-shot |

## What already works (do not rebuild)

- **Ring-3 FS-exec loader** `src/os/kernel/loader/x86_64_fs_exec_ring3.spl`
  (`x86_64_fs_exec_enter_image_ring3`) — PML4[0]-safe mapping (splits the kernel
  2 MiB identity page into a private 4K PT), inline SysV frame, ring-3 iretq.
- **Shell-facing spawn** `x86_64_fs_exec_spawn.spl` (`x86_64_fs_exec_spawn`) ←
  `fs_exec_spawn_ring3(path,argv,envp)` (`fs_exec_spawn.spl:272`, does not return on
  success). Reads the ELF from FAT post-vmm via `_x86_64_read_spawn_bytes_and_blob`.
- **Kernel prereqs**: `EFER.NXE` (cpu.spl), `environ` (crt0.S), native `exit`
  syscall (baremetal_stubs.c `rt_syscall_dispatch` case 0), `vmm_map_nvme_bar_high()`
  after `vmm_init`.
- **Merged SSH+ring-3 boot** `arch/x86_64/ssh_ring3_entry.spl`:
  `arch_x86_64_early_init` + `rt_x86_tss_init` + `simpleos_nvme_init` + `rt_net_init`
  (all BEFORE vmm) → `pmm_init_identity_range` + `vmm_init` + `vmm_map_nvme_bar_high`
  → `SshDaemon.start()`.
- **rv64 SSH login is proven** (durable transcripts `build/os/rv64-ssh-live.*`).
  **x64 SSH login is NOT proven** — see the blocker.

## Reproducible build + boot (merged x64 SSH+ring-3 kernel)

```bash
SEED="src/compiler_rust/target/release/simple"
# 1. build markers the entry/build require (NOT auto-generated for x64 — see gap below)
mkdir -p build/os/generated/generated
printf 'pub fn ssh_live_build_marker() -> text:\n    "ssh-ring3-build:manual"\n' \
  > build/os/generated/ssh_live_build_marker.spl
# (also build/os/generated/generated/simpleos_log_config.spl with simpleos_log_compile_* stubs)
# 2. native-build the merged kernel
SIMPLE_BOOTSTRAP=1 SIMPLE_LIB="$PWD/src" SIMPLE_OS_LOG_MODE=off SIMPLE_ALLOW_FREESTANDING_STUBS=1 \
  "$SEED" native-build --source build/os/generated --source src/os --source src/lib \
  --source examples/09_embedded/simple_os --backend cranelift --cpu x86-64-v1 \
  --opt-level=aggressive --log off --entry-closure \
  --entry examples/09_embedded/simple_os/arch/x86_64/ssh_ring3_entry.spl \
  --target x86_64-unknown-none -o build/os/simpleos_ssh_ring3.elf \
  --linker-script examples/09_embedded/simple_os/arch/x86_64/linker.ld
# 3. boot with net (2222->22) + NVMe disk (clang hello staged as /FSEXEC.ELF)
qemu-system-x86_64 -no-user-config -monitor none -nographic -no-reboot -machine q35 -cpu qemu64 -m 2G \
  -kernel build/os/simpleos_ssh_ring3.elf -serial file:build/os/x64-ssh-ring3.serial.log \
  -device isa-debug-exit,iobase=0xf4,iosize=0x04 \
  -drive file=build/os/hello/fat32-hello.img,if=none,id=nvm,format=raw -device nvme,serial=deadbeef,drive=nvm \
  -netdev user,id=n0,hostfwd=tcp::2222-:22 -device virtio-net-pci,netdev=n0 &
# 4. after "[sshd] accept loop start": ssh -p 2222 root@127.0.0.1 <cmd>  (askpass password "simpleos")
```

Known build-infra gap: the `ssh_live_build_marker` is auto-generated only for
riscv64 targets (`os_build_run.spl:203` `_is_riscv64_live_helper_target`); x64
needs it hand-written (above) or that gate extended to `_is_ssh_live_target`.

## Critical path — the ONE blocker (root-caused)

**x64 SSH login fails at version exchange.** The sshd accepts the TCP connection,
sends its banner, and the client version arrives correctly on the C side
(`[tcp-recv-version] text=SSH-2.0-OpenSSH_9.6p1`), but the Simple-side `[u8]` of
that version reads back **corrupt** (`version raw bytes … hex=57579a57…`,
length 41 correct, values wrong), so `_ssh_identification_bytes_start_ssh2` fails,
the session falls to a second `rt_net_recv_version_text` take which returns empty
(the version was already consumed), and it aborts "invalid client version".

**Root cause is NOT the sshd** (filed:
`doc/08_tracking/bug/x64_sshd_version_exchange_freestanding.md`). Traced to the
core: the C runtime is internally consistent —
`_tls_runtime_array_from_bytes` (baremetal_stubs.c:10325) builds the array as
`runtime_array_inline_items(out)[i] = ENCODE_INT(buf[i])` and sets `out->items` to
that inline location; `rt_bytes_u8_at` (:9623) reads
`_rv_byte(runtime_array_items(arr)[idx])`; `runtime_array_items` (:310) returns
`a->items`; `_rv_byte` (:6212) does `IS_INT(v)?DECODE_INT(v):v`. Build and read are
both C in one file with the same structs → C→C is exact. The value corrupts only as
the `[u8]` `RuntimeValue` **round-trips through the Simple x86_64 freestanding
native-build codegen** (C `rt_boot_tcp_take_version_bytes` → Simple facade
`rt_net_recv_version_bytes` → Simple `do_version_exchange` locals → C
`rt_bytes_u8_at`). This is a **C↔Simple `RuntimeValue`/`[u8]` ABI / representation
mismatch on the x64 freestanding native-build path** (heap-pointer tag / calling
convention across the C boundary).

Corroboration (same class elsewhere on x64 freestanding):
- The ring-3 loader deliberately AVOIDS `[u8]` and parses the ELF via `mmio` on a
  raw buffer (`x86_64_fs_exec_ring3.spl`), because `[u8]` element reads were garbage.
- The prod entry's magic check prints `magic=248,3,0,0` for a valid ELF `[u8]` and
  the loader ignores it, reading via mmio instead.

**Why this is the gate, not a sshd reorder:** the whole SSH protocol (version →
KEX → packet → auth) is `[u8]`-based; a version-exchange reorder to a text-first
path would still need `char_at`/text→bytes reconstruction (also flagged unreliable,
`ssh_session.spl:806-808`) to compute the KEX exchange hash H over the exact V_C
bytes, and it would risk the proven rv64 lane. Fixing the ABI unblocks the entire
x64 SSH protocol at once.

## Ordered remaining steps

1. **[GATE — compiler/runtime, LARGE] Fix the x64 native-build `RuntimeValue`/`[u8]`
   ABI.** Make Simple x86_64 freestanding native-build pass heap `RuntimeValue`s
   (esp. `[u8]` arrays) to/from the C runtime with the exact representation the C
   runtime uses (`ENCODE_PTR`/`DECODE_PTR`, tag bits, calling convention). Minimal
   repro: a Simple fn that calls a C fn returning a `[u8]` built by
   `_tls_runtime_array_from_bytes`, then reads it back with `rt_bytes_u8_at` and
   asserts the bytes — compare interp vs x64 native-build. This unblocks x64 SSH
   login AND removes the `[u8]`-via-mmio workarounds in the loader. Needs broad
   re-verification (all `[u8]` interop).
2. **[SMALL] Route the exec dispatch to a real spawn.** In
   `ssh_session_channel.spl _do_live_interactive_fast_path`, for a command that
   resolves to a FAT path (accept an absolute `/…ELF` directly), call
   `fs_exec_spawn_ring3(path, [path], [])` (import from
   `os.kernel.loader.fs_exec_spawn`) instead of the text-report branch
   (`ssh_exec_fat_launch_line`). On spawn success control never returns. CAUTION:
   this pulls the loader into the net-only `ssh_live_entry.spl` link too — verify
   that build still succeeds, or guard the import to the ring-3 entry.
3. **[SMALL] One-shot demo harness** `scripts/os/ssh_clang_hello_ring3.shs`: build
   the merged kernel (above), stage the clang hello as `/FSEXEC.ELF` (reuse
   `examples/09_embedded/simpleos_hello_c/patch_fsexec_image.spl`), boot with net +
   NVMe, wait for `[sshd] accept loop start`, run `ssh -p 2222 root@127.0.0.1
   /FSEXEC.ELF` (askpass password `simpleos`), gate the serial log on `hello from
   clang on simpleos` + `[user] exit rc=42`.
4. **[LARGE — defer] Interactive shell / return-to-scheduler.** For multiple
   commands over one SSH session, ring-3 exit must return to the scheduler instead
   of `isa-debug-exit`. Not required for the one-shot demo.

## Risk summary

The only remaining risk is item 1 (the x64 `RuntimeValue`/`[u8]` ABI fix) — a core
compiler/runtime change with broad `[u8]` impact, so it needs its own careful change
and system-wide re-verification. Everything else (2–3) is mechanical and gated on
it; item 4 is out of scope for `ssh guest run /ELF`. Items proven this session
(fork builds, boots, sshd listens post-vmm, net survives vmm, TCP + version banner)
are no longer risks.

## 2026-07-10 status — SSH login DONE, one blocker left on the demo

The blocker in "Critical path" above is **RESOLVED**. The x64 `[u8]` C↔Simple ABI
was root-caused (packed-byte vs tagged-slot representation) and fixed
(origin `19e2f81e` packed contract, `7dc03ab5` if-expr phi-merge workaround,
`ee0d17c7` version-transcript fixes). **x64 SSH login now completes end-to-end
with a real OpenSSH client** — full KEX → NEWKEYS → password auth (`simpleos`) →
channel → `debug1: Exit status 0` (evidence `build/os/ssh_client.log`).

Ledger now:
| Piece | State |
|-------|-------|
| x64 SSH LOGIN (version→KEX→auth→channel) | **DONE** (ee0d17c7; real client, Exit status 0) |
| SSH exec dispatch → `fs_exec_spawn_ring3` | **WIRED** (fires at runtime; byte-predicate path detect; builds 170/0) |
| SSH→ring-3 one-shot demo runs the ELF | **BLOCKED** — see below |

**Remaining blocker (the ONLY thing between here and the full goal):**
`simpleos_fat32_stream_open("/FSEXEC.ELF")` returns **0** in the merged SSH kernel
while the non-SSH prod entry reads **13888** from the *same image* via the *same
extern calls* (disk image verified good — FSEXEC dirent + ELF magic + hello
string all present). Filed:
`doc/08_tracking/bug/x64_ssh_kernel_fat32_stream_open_zero.md`. Prime suspects:
(1) NVMe/FAT DMA state vs `rt_net_init` ordering in `ssh_ring3_entry.spl`;
(2) `text` path mis-marshal on x64 freestanding
(`doc/08_tracking/bug/x64_freestanding_text_char_at_starts_with.md`). Isolation:
mirror the prod `_read_fsexec_bytes` verbatim, positioned right after
`simpleos_nvme_init` (before `rt_net_init`), and compare the stream_open rc.

Compiler root fixes still pending (all worked around, documented): if-expr
phi-merge, chained-method mis-lowering, extern-`[u8]`-return-into-typed-store,
text `char_at`/`starts_with` mis-decode.
