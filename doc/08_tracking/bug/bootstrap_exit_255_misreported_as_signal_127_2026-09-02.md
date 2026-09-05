# `bootstrap-from-scratch.sh` misreports exit 255 as "signal 127" — misdirected the Stage 3 investigation for four runs

Date: 2026-09-02
Status: root cause of the misreport identified; the underlying Stage-3 crash it was
masking is FIXED (see RETRACTION below). The status-rendering bug itself is still
open and worth fixing on its own.
Site: `scripts/bootstrap/bootstrap-from-scratch.sh:3092` (signal computation),
`src/compiler/50.mir/_MirLowering/module_lowering.spl:369`
(`record_external_layout_reference`, the real Stage-3 crash site, fixed).

## RETRACTION

This record originally concluded that Stage 3 self-host was killed by an
out-of-memory event ("signal 127", host swap exhausted) during
`phase4:monomorphize`. **That conclusion was wrong.** There is no signal 127 —
POSIX signal numbers top out around 64, and 127 does not correspond to any
kill. The doc under this filename previously (mis)named the failure
`stage3_monomorphize_killed_signal127_host_swap_exhausted_2026-09-02.md`; it has
been renamed to describe what the defect actually is.

The real cause was a **SIGSEGV (raw exit status 255)** in
`record_external_layout_reference` at
`src/compiler/50.mir/_MirLowering/module_lowering.spl:369` — a bare `.unwrap()`
call on an `Option` returned by `self.symbols.get_symbol_raw(symbol.id)`. This
is the "stolen unwrap" defect class already known in this repo: any module that
publishes its own bare `unwrap` (e.g. `Poll`, `FailSafeResult`) can steal the
binding that `Option.unwrap` resolves to, so the call returns raw `0` instead of
the real value or a controlled failure. Simple's nil sentinel is raw `3`, not
`0`, so a `!= nil` check cannot screen the stolen result — it segfaults instead.

Fixed in PR #291 (branch `work/stage3-segv-unwrap`, commit `bb2f1c380ee`,
"fix(mir): stolen `unwrap` segfaults record_external_layout_reference — the
real Stage-3 blocker") by replacing the bare `unwrap()` entirely: an initial
`.?` presence guard (`if not symbol_info.?: return`) is followed not by
`.unwrap()` but by a `match` on `Some`/`nil`, dispatching the resolved value
to a new `record_external_layout_reference_resolved` helper without ever
calling `unwrap`. Calling no `unwrap()` at all — guard or no guard — is what
makes the fix safe: the vulnerable pattern earlier in this record is a `.?`
guard *followed by* `.unwrap()`, which the stolen binding still intercepts
regardless of the guard. `match`/`case Some` is immune because it dispatches
no method name, so there is nothing for the stolen `unwrap` binding to hijack.

**Confirmed, not assumed:** subsequent Stage-3 runs on the fixed tree exit with
status **1** (a normal, attributable failure/success code), not 255, and
produce no crash report. The most recent run's peak RSS was **~123 MB** —
nowhere near the multi-GB swap exhaustion this record originally blamed.
Memory was never the blocker.

## The actual defect: exit 255 renders as "signal 127"

`scripts/bootstrap/bootstrap-from-scratch.sh:3092` computes the reported signal
number as:

```sh
stage3_signal=$((stage3_status - 128))
```

A child killed by a real signal N exits with shell status `128 + N` (POSIX
convention), so this line is correct for genuine signal deaths — e.g. status
139 (SIGSEGV, N=11) or status 143 (SIGTERM, N=15). The line's guard,
`elif [ "${stage3_status}" -gt 128 ]`, is the problem: **exit code 255** (a
crash reported by some paths as a raw negative/`-1`-style status, or a shell
wrapping a process that died with a status the kernel could not attribute to a
specific signal number in this reporting path) also satisfies `-gt 128`, and
`255 - 128 = 127`. There is no signal 127. The script prints:

```
warning: stage3 self-host was KILLED by signal 127 (unknown), not a compile failure
```

`kill -l 127` legitimately returns "unknown" — the script does render that
correctly — but the surrounding sentence still asserts a signal death occurred,
which for status 255 is not established. The fix belongs in this arithmetic:
status 255 should be reported as an ordinary abnormal exit (or, if a genuine
signal underlies it on this host/shell combination, that signal should be
determined some other way — e.g. reading the wait status directly per the
"never read exit status through a pipe" rule used elsewhere in this repo) rather
than folded into the same `-gt 128` bucket as real 128+N signal deaths.

## Why the OOM hint didn't correct the misreading

The same block only offers its out-of-memory hint for the two signals that are
actually associated with memory-pressure reapers:

```sh
if [ "${stage3_signal}" -eq 15 ] || [ "${stage3_signal}" -eq 9 ]; then
  echo "  hint: check for an out-of-memory reaper (earlyoom/systemd-oomd: ...)"
fi
```

For the fabricated "signal 127" this branch never fires, so the script itself
gave no OOM hint. The OOM/swap-exhaustion theory was independently constructed
during investigation from host memory readings taken at kill time (swap 9.3 GB
of 10.2 GB committed) — a real observation, but a coincidental one: the host
happened to be memory-pressured while the SIGSEGV was also occurring, and nothing
in the script encouraged connecting the two. This is worth recording precisely
because it explains how a plausible, partially-evidenced theory persisted
across four separate debugging runs before the actual crash site was found.

## Worked example: how a status-rendering bug misdirected four runs

1. Run 1-3: Stage 3 died at `phase4:monomorphize` with the script reporting
   "signal 127", host swap near its ceiling. The investigation reasonably
   treated this as an OOM kill and spent its effort on memory levers:
   `SIMPLE_NATIVE_BUILD_THREADS=1` (cut steady-state RSS ~10x, peak unchanged),
   the compiler's low-memory path (gated off for Stage 3 by design), `purge`
   (needs root, unavailable), reaping stale processes (no material gain).
2. None of these levers changed the outcome, because none of them addressed
   the actual crash — a segfault in MIR lowering that happens to occur near
   where monomorphize runs in the phase sequence, on a host that also
   happened to be swap-pressured.
3. Run 4 examined the raw exit status directly instead of trusting the
   script's "signal 127" label, found it was 255, and worked out that
   `255 - 128 = 127` is exactly the arithmetic bug above — 127 was never a
   real signal number to begin with. That reframed the search from "find more
   free RAM" to "find what segfaults", which led directly to the bare
   `.unwrap()` in `record_external_layout_reference`.

The general lesson: a self-reported diagnostic string ("KILLED by signal N")
is only as trustworthy as the arithmetic that produced it. When a reported
signal number doesn't correspond to a real signal (here, N=127; POSIX signals
run 1-64), treat the reporting mechanism itself as suspect before building a
root-cause theory on top of it.

## Fix direction for the rendering bug itself

`stage3_status -gt 128` is too broad a test for "this was a signal death".
Options:
- Cap the accepted range explicitly, e.g. `stage3_status -gt 128 && stage3_status -le 192`
  (128+64, the highest real POSIX signal), and report anything above that as a
  plain abnormal exit rather than a fabricated signal.
- Read the child's wait status directly (not through a derived numeric exit
  code) so real signal deaths and other abnormal exits are distinguished at
  the source, per the pattern already fixed for `shell()` in
  `doc/08_tracking/bug/shell_collapses_every_signal_death_to_minus_one_2026-08-17.md`.

This has not been fixed yet in `bootstrap-from-scratch.sh` — this record exists
to name the defect precisely and prevent the same misreading from recurring.

## Related

- PR #291 (`work/stage3-segv-unwrap`, `bb2f1c380ee`) — the actual Stage-3 fix.
- `doc/08_tracking/bug/shell_collapses_every_signal_death_to_minus_one_2026-08-17.md`
  — the sibling defect class: exit-status information lost or fabricated between
  a child process and the code that reports on it.
- The separate, still-open `E-MIR-TYPE-ZeroKind` investigation that this
  record's original version incorrectly said was blocked on host memory. It is
  no longer blocked by that; MIR function lowering is reachable now that Stage
  3 no longer segfaults before reaching it.
