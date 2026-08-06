# QEMU launch scripts used `-device isa-debug-exit` — board-runnable rule violation

- **Filed:** 2026-08-06
- **Status:** PARTIALLY FIXED — 12 scripts fixed, 10 scripts + 7 out-of-lane
  `scripts/check/` scripts still violate, documented below
- **Area:** `scripts/os/*.shs` (QEMU launch), `scripts/check/*.shs` (out of
  lane for this fix — flagged only), guest-side exit path
  `src/lib/nogc_async_mut_noalloc/baremetal/x86/semihost.spl`,
  `src/lib/nogc_async_mut_noalloc/baremetal/common/test_harness.spl`
- **Rule invoked:** `.claude/rules/board-runnable.md` — "never QEMU `-kernel`
  pass semantics and never `isa-debug-exit`" — a QEMU-only exit mechanism with
  no real-hardware equivalent.

## 1. The violation

`-device isa-debug-exit,iobase=0xf4,iosize=0x04` exists only in QEMU. Writing
a byte to port `0xF4` makes the **QEMU process itself** exit with a code
derived from the written value — there is no port `0xF4` device on real x86
hardware, so any test-completion signal that depends on it cannot run
unmodified on the dev board.

29 files under `scripts/` reference `isa-debug-exit,iobase=0xf4`. 22 are under
`scripts/os/*.shs` (this lane); 7 are under `scripts/check/*.shs` (out of
lane — listed for completeness, not touched here).

## 2. Two genuinely different usage patterns found

Investigation (grep for `QEMU_PID=$!` / `trap ... kill` vs foreground
`RC=$?` / `guest_rc=$?` / `code=$?` capture immediately after the
`qemu-system-x86_64` invocation) showed the 22 `scripts/os/` scripts split
into two families with different fix difficulty:

### 2a. FIXED — 12 scripts: device was vestigial, pass/fail already comes from serial-log grep

These scripts launch QEMU **backgrounded** (`... &`, `QEMU_PID=$!`,
`trap 'kill "$QEMU_PID" ...' EXIT`) and always terminate it with `kill`, not
by waiting for it to self-exit. The QEMU process's own exit code is never
read (no `$?` capture after the invocation). Pass/fail is determined entirely
by `grep -qa <marker> "$SERIAL"` against the `-serial file:$SERIAL` log. The
`-device isa-debug-exit` line was present only "for machine-config parity"
(confirmed by a stale comment in `ssh_lld_link_uefi.shs:26-30`, now
corrected) and had zero effect on the verdict.

Fixed by deleting the `-device isa-debug-exit,iobase=0xf4,iosize=0x04 \`
line from each QEMU invocation:

- `scripts/os/ssh_simple_hello_uefi.shs`
- `scripts/os/ssh_lld_link_uefi.shs` (+ corrected stale header comment)
- `scripts/os/ssh_ring3_uefi_boot.shs`
- `scripts/os/fhs_path_exec_gate_uefi.shs`
- `scripts/os/scp_retrieve_over_ssh_uefi.shs`
- `scripts/os/ssh_b1_witness_uefi.shs`
- `scripts/os/ssh_clang_hello_ring3.shs`
- `scripts/os/ssh_multi_cmd.shs`
- `scripts/os/build_clang_over_ssh_inc2.shs` (+ corrected stale FAIL-message text)
- `scripts/os/build_clang_over_ssh.shs` (+ corrected stale header/FAIL-message text)
- `scripts/os/build_spawn_wait_ring3.shs`
- `scripts/os/scp_retrieve_over_ssh.shs`

**Verification (sabotage-style, on `ssh_simple_hello_uefi.shs`):** ran the
script end-to-end before and after the edit (`SKIP_KERNEL=1`, real OVMF pflash
+ existing `build/os/elfexec_simple/fat32-simple.img`, real sshpass/ssh
dispatch). Both runs produced the byte-identical gate ladder:

```
[ok]   L1 OVMF -> GRUB-EFI app ran
[ok]   L2 multiboot handoff -> kernel _start
[ok]   L3 sshd ring-3 accept loop
[ok]   L4a sshd deferred exec dispatched
[MISS] L4b in-guest simple interpreter printed hello
FAIL: hello output not observed (see serial tail above)   exit=1
```

The L4b miss is a pre-existing, unrelated failure in this environment (not
caused by, or fixed by, this change) — logged separately if not already
tracked. The relevant proof is that **removing `isa-debug-exit` changed
nothing**: same gates, same verdict, same exit code, confirming the QEMU
process's own exit status was never load-bearing for this script family. The
actual pass/fail logic (`grep -qa "hello from simple on simpleos" "$SERIAL"`)
never reads QEMU's exit code at all — it is a pure serial-log sentinel check,
which is exactly the board-runnable-compliant pattern (real hardware can also
be scraped over a real UART).

### 2b. NOT FIXED — 10 scripts: device is the guest's actual exit signal

These scripts run QEMU either in the **foreground** or under a wrapper, and
capture the process exit code directly afterward (`RC=$?`, `guest_rc=$?`,
`code=$?`), or (in `build_clang_stream_ring3.shs:112`, explicit comment) rely
on "the bare-exec dispatcher's exit(0) halts QEMU via isa-debug-exit
directly" as the mechanism that lets the script's shell resume at all. In this
family the guest's exit path performs `outb(0xF4, code)` (see
`src/lib/nogc_async_mut_noalloc/baremetal/x86/semihost.spl:99-103`
`qemu_exit()`, and `test_harness.spl:69-81` `test_end()`) and there is
**no other exit signal in the guest kernel/runtime for these entry points** —
removing the device would either hang the script until timeout or make
`$?`/`RC` read QEMU's ordinary SIGTERM/kill exit status instead of the guest's
real result, silently turning every result into a false pass or false fail:

- `scripts/os/abi_probe_run.shs`
- `scripts/os/text_char_at_store_probe_run.shs`
- `scripts/os/clang_argv_tokenize_probe_run.shs`
- `scripts/os/modinit_probe_run.shs`
- `scripts/os/run_simpleos_q35_smoke.shs`
- `scripts/os/build_clang_stream_ring3.shs`
- `scripts/os/build_clang_disk.shs`
- `scripts/os/build_fsexec_prod_ring3.shs`
- `scripts/os/build_fsexec_general_ring3.shs`
- `scripts/os/build_fsexec_stream_ring3.shs`

## 3. Recommended fix for the 2b family (not implemented — substantial, deferred)

`test_harness.spl:69-81` already shows the right shape: it prints a
deterministic sentinel line over serial (`[TEST END] passed=N failed=N`)
*before* calling `outb(0xF4, exit_value)`. The general fix is:

1. **Guest side:** every exit path used by the 2b scripts (the FS-exec/
   heap-spawn "kernel resumed" ladder, the raw probe entries under
   `examples/09_embedded/simple_os/arch/x86_64/*_entry.spl`) must print a
   well-defined line to COM1/serial *before* any `outb(0xF4, ...)` — e.g.
   `SIMPLEOS-TEST-RESULT: PASS` / `SIMPLEOS-TEST-RESULT: FAIL rc=<n>` — and
   then simply **halt** (`hlt` loop) instead of exiting QEMU, exactly the way
   real hardware would sit at completion.
2. **Host side:** each of the 10 scripts switches from `RC=$?`/`code=$?`
   process-exit detection to `grep -qa "SIMPLEOS-TEST-RESULT: PASS" "$SERIAL"`
   against the serial log, with a `BOOT_WAIT`-style polling loop plus explicit
   `kill "$QEMU_PID"` — the exact pattern already used by the 12 scripts fixed
   in §2a.
3. Only after every entry point in the ladder emits the sentinel can
   `-device isa-debug-exit` be dropped from these 10 invocations.

This touches guest-side freestanding entry code across several probe/ladder
families (not just shared library code), which is why it was **not** folded
into this change — it needs its own verification pass per entry point
(sabotage-testing a guest kernel crash path is materially more involved than
a host-side shell script edit). Scope kept to the low-risk §2a set per the
board-runnable rule's own guidance: don't force a fix that risks breaking a
working QEMU-based harness.

## 4. Out-of-lane: `scripts/check/*.shs` (not touched, flagged for a follow-up pass)

7 files under `scripts/check/` also register `-device isa-debug-exit` and were
not investigated or touched by this change (different lane / concurrent work
risk):

- `scripts/check/check-freebsd-wm-seam-refusal.shs`
- `scripts/check/check-simpleos-servers-qemu.shs`
- `scripts/check/check-simpleos-usb-xhci-qemu.shs`
- `scripts/check/check-simpleos-wm-aqua-glyph-ovmf-evidence.shs`
- `scripts/check/check-simpleos-wm-host-seam-evidence.shs`
- `scripts/check/check-simpleos-x86-64-wm-hello-lifecycle-evidence.shs`
- `scripts/check/check-simpleos-wm-visible-display-evidence.shs`

Each should be triaged with the same backgrounded-vs-foreground test used in
§2 before editing.

## 5. Separate finding, not in scope here

`scripts/os/ssh_clang_hello_ring3.shs`, `scripts/os/ssh_multi_cmd.shs`, and
`scripts/os/scp_retrieve_over_ssh.shs` boot with `-kernel "$KERNEL"` rather
than OVMF pflash — also a `board-runnable.md` violation ("never QEMU
`-kernel` pass semantics") independent of the isa-debug-exit issue fixed
here. Not touched in this change; needs its own investigation into whether an
OVMF-pflash boot path is feasible for these three gates.
