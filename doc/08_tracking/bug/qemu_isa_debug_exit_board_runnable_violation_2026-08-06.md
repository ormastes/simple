# QEMU launch scripts used `-device isa-debug-exit` — board-runnable rule violation

- **Filed:** 2026-08-06
- **Status:** PARTIALLY FIXED — 16 scripts fixed (12 original + 4 more in the
  2026-08-06 follow-up pass), 3 confirmed-genuine + 3 likely-safe-unverified
  `scripts/os/` scripts remain, plus 7 out-of-lane `scripts/check/` scripts
  still violate, documented below (§2b-revised, §4). The separate
  `-kernel`-boot finding (§5, 3 scripts) was investigated 2026-08-06: no
  miscitation as board-runnable evidence found anywhere in the repo (false
  alarm) — closed with DEV-HARNESS-ONLY banners added to the 3 scripts; the
  underlying OVMF-port gap for 2 of them remains open and tracked separately.
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

### 2b-revised (2026-08-06, follow-up pass). Re-triaged: only 2 of the original
10 actually gate on the exit code; 4 were reclassified and FIXED like §2a; 3
are un-gated but left unconverted for lack of build artifacts this session;
1 (`run_simpleos_q35_smoke.shs`) is confirmed genuinely 2b.

The original blanket classification ("RC=$?/guest_rc=$?/code=$? capture" ⇒
2b) was too coarse: several scripts capture `RC=$?` **only to echo it** into
the log for human debugging, with the actual verdict coming entirely from
`grep -q <marker> "$SERIAL_LOG" && echo PASS || echo MISS` lines that never
gate the script's own exit code (the script always returns 0). Capturing and
printing `$?` is not the same as depending on it. Re-checked each of the 10
individually:

**FIXED — 4 probe scripts, same pattern as §2a (device was vestigial):**
`abi_probe_run.shs`, `modinit_probe_run.shs`,
`text_char_at_store_probe_run.shs`, `clang_argv_tokenize_probe_run.shs`. None
of these four ever read `$?`/`RC` at all (verified by grep before editing) —
pass/fail is a pure `grep -aE '^P'`/`'^(P|M)'`/`'^\[probe\]|^PROBE'` serial-log
scrape, informational (the script itself always exits 0). Fixed by deleting
the `-device isa-debug-exit,iobase=0xf4,iosize=0x04 \` line from each. **Sabotage
verification:** ran each script before and after the edit with a fresh
`native-build` (no pre-existing artifacts, so each run rebuilds from scratch).
All four are currently hitting a pre-existing, unrelated failure in this
environment — the guest never reaches its `PD`/marker print, serial log is
empty, `timeout` fires at `QEMU_TIMEOUT` (20s) — **not caused by, or fixed by,
this change**. Before and after are byte-identical modulo the QEMU child pid
and the `Time:` build-duration line; same exit code (0), same empty serial
log, same timeout-kill message. This is the same proof shape as the
`ssh_simple_hello_uefi.shs` verification in §2a: removing the device changed
nothing observable.

**LIKELY SAFE, NOT CONVERTED (no build artifacts to verify against this
session) — 3 scripts:** `build_fsexec_general_ring3.shs`,
`build_fsexec_stream_ring3.shs`, `build_clang_stream_ring3.shs`. All three
capture `RC=$?` but only `echo` it — none of the three `exit`/`fail` on it,
and the pass/fail signal is entirely the `grep -q <marker> ... && echo PASS
|| echo MISS` block below the capture, which also never gates the script's
final exit code. `build_clang_stream_ring3.shs`'s comment ("the bare-exec
dispatcher's exit(0) halts QEMU via isa-debug-exit directly") describes why
the device makes QEMU terminate *promptly*, not why the verdict depends on
it — with the existing `timeout "$QEMU_TIMEOUT" qemu-system-x86_64 ...`
wrapper already in place, removing the device should only change wall-clock
(QEMU runs to the timeout instead of self-exiting) not correctness. Not
converted here because their required disk images
(`build/os/fat32-fsexec.img`, `build/os/fat32-clang.img`) were not present
in this session and building them was out of budget for this pass — do not
convert without a real before/after run once those artifacts exist.

**CONFIRMED GENUINELY 2b — 3 scripts, hard-gated on the QEMU exit code:**

- `scripts/os/build_clang_disk.shs:56-61` —
  `guest_rc=$?; ... [ "$guest_rc" -eq "$expected_rc" ] || fail ...` — the
  script's own pass/fail hinges on the numeric exit code isa-debug-exit
  produces.
- `scripts/os/build_fsexec_prod_ring3.shs:230-234` —
  `RC=$?; ...; [ "$RC" -eq 3 ] || fail "QEMU exit rc=$RC expected=3"` — same
  hard gate (also separately checks a serial marker, but the RC gate runs
  first and is unconditional).
- `scripts/os/run_simpleos_q35_smoke.shs:137-140` —
  `code=$?; ...; if [ "$code" -ne 1 ]; then ... exit 1; fi` — hard gate on
  `code -eq 1`, evaluated *before* the (already fairly complete) marker checks
  further down, including an existing `TEST PASSED` sentinel line the guest
  already emits. Converting this one is probably the cheapest of the three
  (the sentinel infrastructure the recommended fix in §3 asks for already
  exists in the guest output) but still needs the guest's post-print behavior
  changed from "exit via outb(0xF4,...)" to "halt-loop", rebuilt, and
  boot-verified — not done in this pass.

These 3 are the scripts §3's guest-side sentinel fix genuinely applies to.

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
§2 before editing. Not attempted in the 2026-08-06 follow-up pass either
(time/budget went to re-triaging and converting the `scripts/os/` family
first, per the doc's own guidance that this set is out of lane / concurrent-
work risk).

## 5. Separate finding, investigated 2026-08-06 — FALSE ALARM (not a miscitation)

`scripts/os/ssh_clang_hello_ring3.shs`, `scripts/os/ssh_multi_cmd.shs`, and
`scripts/os/scp_retrieve_over_ssh.shs` boot with `-kernel "$KERNEL"` rather
than OVMF pflash — on its face a `board-runnable.md` violation ("never QEMU
`-kernel` pass semantics"). `board-runnable.md` permits QEMU `-kernel` for
fast dev iteration as long as it is never conflated with board-runnable
proof, so the actual question is whether any doc/report/state file cites
these three scripts' output AS board-runnable evidence.

**Investigation:** grepped every `doc/**/*.md` and `.spipe/**/state.md` that
mentions any of the three script basenames (13 files) for co-occurrence with
"board-runnable"/"board proxy" language. Result: **no miscitation found.**

- `scp_retrieve_over_ssh.shs` already has a compliant OVMF sibling,
  `scripts/os/scp_retrieve_over_ssh_uefi.shs` (one of the 12 fixed in §2a of
  this same doc). Every current active-lane doc that needs board-runnable
  evidence for the getfile/retrieve gate — `.spipe/simpleos_harden_p6_toolchain/state.md`,
  `.spipe/simpleos_clang_simple_migration/state.md`,
  `doc/03_plan/os/in_guest_clang_selfhost_board_plan.md` — cites the `_uefi`
  variant by name, never the plain `-kernel` one.
- `doc/03_plan/os/in_guest_clang_selfhost_board_plan.md` (the plan doc this
  whole clang-on-SimpleOS effort is tracked against) is explicit and honest
  about the gap: it flags the `-kernel`-only clang-retrieve proof as an
  "⚠️ OPEN GAP — ... violates the plan's own 'no QEMU-only mechanism' rule"
  (lines 8-11, 13) and records it as *closed* only once superseded by the
  OVMF path (`2f RESOLVED`, commit `7cf0b6aec3a`, which is exactly
  `scp_retrieve_over_ssh_uefi.shs`).
- `ssh_clang_hello_ring3.shs` and `ssh_multi_cmd.shs` have **no** OVMF
  sibling yet — the one-shot clang-hello demo and the multi-command ring-3
  resume gate have not been ported off `-kernel`. But every reference found
  (`doc/03_plan/os/spipe_next_items_2026-07-11.md`,
  `doc/05_design/os/ssh/simpleos_ssh_ring3_exec_plan.md`,
  `doc/03_plan/os/in_guest_clang_selfhost_board_plan.md`) cites them only as
  ordinary QEMU dev gates ("clang gate", "one-shot demo harness") — none
  asserts or implies board-runnable status from their output.

**Fix applied (hygiene, not a defect fix):** added an explicit
"DEV-HARNESS ONLY — NOT board-runnable evidence" banner comment to all three
scripts, naming `scripts/os/scp_retrieve_over_ssh_uefi.shs` as the
board-proxy equivalent (existing, for the retrieve gate) or pointing at the
tracked porting gap in `in_guest_clang_selfhost_board_plan.md` (for the two
without an OVMF sibling yet), so a future citation cannot casually treat
these three as board-runnable proof.

**Not done (real, larger work, left as the open item it already was):**
porting `ssh_clang_hello_ring3.shs` / `ssh_multi_cmd.shs` to OVMF pflash.
That is guest-side freestanding-entry work of the same shape already
described in §3 above for the isa-debug-exit 2b family, tracked at
`doc/03_plan/os/in_guest_clang_selfhost_board_plan.md` Phase 2 ("board-runnable
port") — not folded into this pass.
