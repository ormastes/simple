# A2 record-ring layout diverges from D2/ref_vm's (no head-counter word)

**Status:** RESOLVED (2026-09-13) -- documented as intentionally distinct formats (suggested fix option 2)

Date: 2026-08-07
Found by: Task B3 (cuda_vm per-launch executor)

## Summary

`src/lib/nogc_sync_mut/test_runner/gpu_mailbox.spl` (Task A2)'s
`MailboxArena.append_record`/`drain_records`/`init_record_ring` reserve a
4-byte head-counter word at the RECORD ring base (`record_ring_offset()+0`)
and start the first 12-byte record at `record_ring_offset()+8`.

`src/lib/common/svmg/ref_vm.spl` (Task D2)'s `SvmgVm.write_record` /
`read_records` (the authority the D3 conformance table
(`test/fixtures/svmg/conformance_vectors.spl`) is defined against) writes
records starting directly at `record_ring_base_offset(log_cap)+0`, with NO
head-counter word — the record count is tracked by the host `SvmgVm`
object (`VmRunResult.record_count`), never written into the arena.

These are two different wire formats for "the RECORD ring," both reachable
from an SVM-G host module, and they disagree by exactly 8 bytes of offset
plus the presence/absence of a counter field. A caller that assembles a
program with D1's `svmg_asm`, runs it via a GPU lane, and then drains the
RECORD ring with A2's `drain_records` will silently misread the first
conformance record's `seq`/`pass` fields as a bogus ring `head`/`cap` pair
(or vice versa).

## Impact on B3

Task B3's `svmg_cuda_kernel.ptx` device interpreter and its host-side
`cuda_vm_executor.spl` both follow **D2/ref_vm's format** (no head
counter), since that is what the D3 conformance table's expected records
are checked against (`test/02_integration/svmg/conformance/conformance_suite_spec.spl`'s
`_check_vector` compares `result.record_count` from `VmRunResult`, which
`ref_vm.run()` produces by counting writes, not by reading a stored
counter). `cuda_vm_executor.read_records` decodes records starting at
`ring_base+0` and stops at the first structurally-all-zero record
(matching `ref_vm.read_records`'s documented best-effort fallback for a
caller with only the raw arena and no separately-known count).

A2's `MailboxArena`/`drain_records` are unaffected by this change (B3 does
not call them for record decoding) but remain a live foot-gun for any
future caller that mixes A2's record-ring helpers with a D1-assembled /
D2-conformant program.

## Suggested fix (not done here, out of B3's scope)

Either:
1. Change A2's `MailboxArena` to match D2/ref_vm's no-counter format (drop
   the head word, start records at `ring_base+0`), since ref_vm is the
   conformance authority and the interactive/resident mode design (§3.2)
   does not appear to require a stored record count either -- the
   interactive host already tracks state; or
2. Document the two formats as intentionally distinct ("A2's interactive
   buffered-record ring" vs "D2's batch/conformance record ring") and add
   a loud comment cross-reference in both files so a future reader does
   not assume they interoperate.

Filed rather than silently worked around, per repo policy (fix-or-file,
never route around silently).

## Triage 2026-09-12

Reviewed in the 2026-09-12 bug-db triage sweep (Rule D: filed after 2026-07-29, no runnable repro in the record); left open with a status line added since none existed. Evidence: worktree `simple-bugdb-triage` branch `work/bugdb-triage-2026-09-12`; deployed seed `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple` (50,093,192 B, 2026-09-06 09:59) available for re-verification.

## Resolved 2026-09-13 (BUGFIX-10 fanout)

Applied suggested fix option 2 (documenting the two formats as intentionally
distinct, since no current caller mixes them and unifying the wire formats
would be a behavior change to `MailboxArena`, out of scope for a
documentation-only fix): added a loud, symmetric cross-reference warning
docstring to both `MailboxArena.record_ring_offset()`
(`src/lib/nogc_sync_mut/test_runner/gpu_mailbox.spl`) and `read_records()`
(`src/lib/common/svmg/ref_vm.spl`), each naming this bug id and the other
file, so a future reader cannot assume the two RECORD rings interoperate.

No behavior changed (docstrings only). Re-ran both modules' existing
suites to confirm no regression: `test/01_unit/lib/svmg/ref_vm_spec.spl`
(19/19 PASS) and `test/01_unit/lib/test_runner/gpu_mailbox_spec.spl`
(19/19 PASS), both unchanged from before the edit. No new spec added — a
docstring has no observable behavior to lock with an assertion; the
existing suites already guard the underlying byte-layout logic.

- Status: RESOLVED (2026-09-13) — cross-reference warnings added to both
  files; no code behavior changed.
