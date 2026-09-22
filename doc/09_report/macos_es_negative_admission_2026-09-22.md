# macOS Endpoint Security admission rejection coverage

The P3 bug `macos_full_cli_gui_admission_process_proof_2026-07-27` remains
open. Apple-granted Endpoint Security entitlement and an approved signing
team are external prerequisites. The existing TODO audit classifies this
as REAL-EXTERNAL in `doc/08_tracking/todo/blocked_p1_audit_2026-07-28.md`.

The four existing source contracts exercise unavailable policy, immutable
snapshots, collector state, and provenance. PR #1207 records their prior
macOS passes. The existing unavailable-policy system spec checks build,
verify, and execution rejection. None independently exercises malformed
prepared/admitted signing and entitlement metadata through authenticated
builder bootstrap.

`test/01_unit/scripts/macos_es_missing_identity_contract.shs` adds that
coverage using a temporary Git repository containing the unchanged real
builder and tracked test policies. It checks missing policy plus absent or
unassigned signing identity, absent or malformed team, absent or incorrect
entitlement, and duplicate signing/status keys. Each malformed phase is
tested through build, verify, and verified execution. Complete phase
metadata controls reach the deliberately absent source snapshot, proving
the earlier negative cases fail at the intended policy gate.

All invocations require exit 125, exact diagnostics, empty stdout, and no
build directory. No compiler, signing command, live collector, or GUI is
executed. The fixture removes itself on exit. Production builder and policy
are unchanged; this is regression coverage, not live admission evidence.

Validation on macOS arm64, 2026-09-22: `/usr/bin/time -l sh
test/01_unit/scripts/macos_es_missing_identity_contract.shs` passed all 28
invocations in 36.17 seconds, with maximum child RSS 7,192,576 bytes
(6.86 MiB) and zero swaps. Shell syntax, generated-spec layout (zero `.spl`
files under `doc/06_spec`), and working direct-env guard passed. These
numbers profile this rejection harness, not a live collector. During test
development a positive-control addition exposed a shell-global diagnostic
variable collision in the harness; renaming it resolved that failure.

SoSIX impact: none. This macOS-only contract uses `/bin/sh` syntax and keeps
the existing Darwin immutable-snapshot requirement; it does not change a
portable runtime API or imply Endpoint Security support on another OS.

Remaining external work: provision the approved signing identity and Apple
Endpoint Security entitlement, review and commit a fully pinned prepared
policy, build the signed candidate, independently review and commit admitted
artifact pins, verify admission, then collect canonical full-CLI live GUI
process history. Local negative tests cannot substitute for those steps.

## Restored-worktree revalidation

Reconstructed branch `test/macos-es-negative-admission-20260922` at clean
source `e8abd6f85e5c2983f95d8a177daac7e8afc77306` and executed the unchanged
28-case contract once on macOS 26.5 (25F71), arm64. All cases passed in
33.05 seconds, with maximum child RSS 7,290,880 bytes and zero swaps.
The prior comparable contract took 36.17 seconds and 7,192,576 bytes;
this sample shows lower elapsed time and a 98,304-byte RSS increase, with
no source change or evidence of a material regression.

The external watchdog from reviewed source `bd544ccef9e` ran with
`--rss-cap-mode=enforce --max-rss-kib=5859375 --interval-ms=100
--timeout-seconds=180 --session-mode=new` and observation budget 5000 ms.
Its receipt reports exit 0, `status=complete`, `quiescent=1`, 324 samples,
peak process-tree RSS 15,824 KiB, zero observation overruns, verified session
helper integrity, and no unexpected session PIDs. This is sampled enforcement:
`hard_memory_limit=0`. It does not prove the bootstrap plan's hard memory
containment requirement or any live collector memory behavior.

Evidence is retained under
`/Users/ormastes/simple-tmp/mac-es-negative-admission/build/evidence/macos-es-recheck-20260922/`:
`negative.log` contains the command result and timing; `negative-rss.env`
contains the process-tree receipt. The test SHA256 is
`db64c54740889440add3b95ee1d212cfb703231a2d43eeaf6d3e6db75512df4c`;
the external watchdog SHA256 is
`69349c788f20f2f4052ae7e852baea59ce836c71fa65fad3b6c4226700e1c64f`.

Host admission remains unavailable: `security find-identity -v -p codesigning`
reports zero valid identities. The tracked policy remains unavailable with
unassigned signing identity/team, and no collector artifact exists in this
restored checkout. The tracked XML requests the ES entitlement; it is not
evidence of Apple approval. No signed candidate, prepared/admitted policy,
or live history was produced. The canonical P3 bug stays open.

## Post-spawn rejection cleanup

Further review found a source-level lifecycle gap: `collect()` spawned its
root before `bindRoot()`, which can reject previously detected ES sequence
gaps or pre-root overflow. That exception left the spawned child unreaped
and potentially running. Post-spawn process-group validation had the same
cleanup gap. No live ES entitlement is needed to exercise either boundary.

The collector now owns the successful `posix_spawn` result in `SpawnedRoot`
until a successful wait reaps it. Error cleanup sends SIGKILL to the owned
group only when the unreaped child is its group leader, also signals the
exact child, and reaps it. Successful waits disable cleanup; ECHILD relinquishes
ownership to avoid signaling a potentially reused PID. The scope owner also
cleans up when `bindRoot()` throws. The unavailable policy's source hash is
updated without changing its admission status.

New real-process self-tests verify pre-root rejection with a spawned sleep
process, actual getpgid rejection for a child sharing the collector's group,
reaping, sibling survival, and idempotent cleanup after a successful wait.
The first compiled self-test passed in 4.05 seconds with maximum child RSS
175,685,632 bytes and sampled tree peak 209,312 KiB. A fixture with scope
cleanup disabled failed as expected (exit 1) in 5.43 seconds and still
terminated quiescently; it peaked at 203,712 KiB across the sampled tree.
This confirms the new regression detects the missing cleanup. These times
include Swift compilation and are not a live collector performance benchmark.

Both runs used the reviewed external watchdog with enforced sampled cap
5,859,375 KiB, 100 ms target interval, 180-second timeout and 5000 ms observation
budget. Logs, test binaries, mutant source and receipts are retained under
`build/evidence/macos-es-child-cleanup-20260922/` in this worktree. Neither run
establishes hard memory containment (`hard_memory_limit=0`) or live ES admission.
