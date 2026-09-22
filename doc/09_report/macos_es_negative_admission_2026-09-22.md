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
