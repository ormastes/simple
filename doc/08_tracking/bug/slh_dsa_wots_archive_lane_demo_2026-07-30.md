# `slh_dsa_wots.spl` retype — archive-lane verification demo (2026-07-30)

Assignment (part 2 of 2): re-apply the pass-11 reverted retype
(`base_2b`/`wots_checksum_digits_p`/`wots_msg_to_digits_p`/128s wrappers,
`: list` → `[i64]`, 2 census-counted sites / 5 signature occurrences) and
verify it via the alternative lane proposed in the pass-12 root-cause doc,
since `src/os/crypto` cannot be verified via the standard standalone-probe
both-engine A/B (structural JIT exclusion, proved in pass 12).

## Retype applied

Identical to the pass-11 draft (`fn base_2b(x: [u8], b: i64, out_len: i64)
-> [i64]`, `fn wots_checksum_digits_p(msg_digits: [i64], n: u64) ->
[i64]`, `fn wots_msg_to_digits_p(message_n_bytes: [u8], n: u64) ->
[i64]` with `msg_digits`/`csum_digits`/`out` locals explicitly typed
`[i64]`, and the two 128s thin wrappers retyped to match). Re-applied,
then **reverted again** at the end of this pass — see Verdict.

## Lane 1: `native-build --emit-object` + `objdump` — BLOCKED, PROVED not to be my fix's fault

Built an entry file (`archive_entry_slh.spl`) importing `base_2b` and
`wots_msg_to_digits_128s` from `os.crypto.slh_dsa_wots`, and ran:

```
./bin/simple native-build --entry archive_entry_slh.spl --emit-object -o slh_fixed.o
```

Timed and bounded per instruction (30-min cap). Confirmed via `/proc`
utime polling that the build's real worker process
(`native_build_worker.spl`, a separate child spawned by the outer
`native-build` driver — the outer process itself sits at 0% CPU the
whole time, which is a red herring; do not judge liveness from it) was
genuinely, continuously active (utime climbing steadily across every
poll, ~85-95% of one core) — not stalled or hung.

**Result at ~18 minutes (within the 30-min cap): failed with exit code
1**, not a timeout:

```
[ERROR] MIR error: MIR lowering error: unresolved method call: to_u64
[ERROR] MIR error: MIR lowering error: unsupported MIR type kind: HirTypeKind::Infer((0, 0))
[mir-lower] WARNING: unresolved method call 'to_u64' lowered to const-0 placeholder (silent-null risk, Task #145)
...
[STDERR] error: native-build worker exited with code 1.
```

**PROVED not attributable to this pass's retype**: `grep -n
'slh_dsa\|archive_entry_slh'` against the full 417-line log returns
**zero matches** — none of the errors reference `slh_dsa_wots.spl` or
the entry file at all. `native-build --entry` performs full-project
dependency discovery (it pulled in the whole app graph, not just the
target file and its direct imports), and the errors are pre-existing,
already-tracked (`Task #145`, cited in the log's own warning text)
whole-program MIR-lowering gaps (`unresolved method call: to_u64`,
`unsupported MIR type kind: HirTypeKind::Infer`) hit somewhere else in
that graph — the same general family as the `jit_whole_program_compile_
parser_gap_ot_layout_shaper_2026-07-30.md` finding already on record
from a parallel session this pass observed in `git status` noise. This
is a **pre-existing native-build/whole-program-compile blocker**, not a
consequence of retyping `slh_dsa_wots.spl`.

**Not chased further this pass** (time-bounded): scoping the build to
`--source src/os/crypto` only (rather than full default discovery) might
avoid pulling in the unrelated part of the dependency graph that fails,
but was not attempted — flagged as the next thing to try for whoever
picks this lane up again.

## Lane 2: in-repo NIST KAT spec under the interpreter (semantic check) — inconclusive, timing issue

`test/01_unit/lib/crypto/slh_dsa_128s_spec.spl` (WOTS+/XMSS/FORS/HT
round-trips + reduced-parameter end-to-end KeyGen-Sign-Verify). The
spec's own comment estimates ~12.6s for the reduced-parameter path in
this environment. Observed:
- First attempt: killed by the standing `kill_simple_monitor` 60s
  CPU-guard daemon (a known, previously-documented environment behavior,
  not specific to this spec).
- Second attempt with `SIMPLE_TIMEOUT_SECONDS=280`: hit the outer
  `timeout 300` wrapper — "Process timed out" — meaning the actual test
  run took longer than 280-300s in this environment, well past the
  spec's own ~12.6s estimate (plausibly explained by concurrent
  CPU contention from the simultaneous cargo build and native-build jobs
  this pass ran in parallel, or by whole-test-file compile overhead not
  counted in the spec's own per-test estimate).
- Third attempt with a 900s timeout was still running when this pass's
  time budget required finalizing; **not resolved either way**.

## Verdict

**Lane did not complete end-to-end this pass.** Lane 1 (the primary,
object-code-level lane) hit a real, bounded-and-documented, pre-existing
blocker unrelated to the retype itself — not a "the lane doesn't work"
result, but "the lane, as invoked with default full-project discovery,
currently cannot reach the target file due to an unrelated whole-program
compile gap already tracked elsewhere in this repo." Lane 2 did not
finish within the time available to confirm or refute it.

Per the assignment's own instruction ("if the build wall blocks it, doc
the attempt precisely"): **reverted the retype again**, consistent with
the pass-11 discipline of never landing a `src/os/crypto` change without
completed verification. `slh_dsa_wots.spl` remains unfixed on `main`.

**Recommended next attempt**: scope `native-build` to `--source
src/os/crypto` (or otherwise narrow its discovery root) to avoid the
unrelated whole-program MIR-lowering gap, and budget the KAT spec run
without concurrent CPU-heavy jobs competing for cycles.

