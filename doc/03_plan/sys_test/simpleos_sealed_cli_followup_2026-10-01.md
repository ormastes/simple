# Item 1 sealed CLI negative and adjacent acceptance

Base: PR 2151 head `4cd46825d5214d5340b6c3075ed2faef338bc330`.
Isolated worktree: `D:/wk-item1-test-20261001`.
Branch: `work/item1-tests-20261001`. Owner: item1_continue; merge owner: root.
Scope: selected platform REQ-001, REQ-014 and REQ-016 only.

## Concrete fixes and behavioral gates

| Contract | Production behavior | Executable scenario |
|---|---|---|
| Re-admit changed compiler before cache reuse | Remove the target-only process-local shortcut; the existing persistent cache remains behind current compiler admission and its stamp/input checks | Live CLI suite warms a real default build, changes the explicit compiler to a missing path, and requires refusal in that same process |
| Inspection describes the requested mode | Reject `--debug-gui` with either sealed inspection flag before build/host probes | Pure mode matrix and real CLI negative matrix for default plus four named routes |
| Named ordered argv reaches the child | Existing sealed dispatcher remains the production owner | Real compiled observer receives all four named plans and checks every argv position, stderr and exit |
| Host and artifact identity remain bound | Existing canonical admission owners remain authoritative | All five live routes compare actual Linux/Windows host, QEMU probe digest/version and unchanged QEMU/CLI/provenance/kernel hashes |
| Guest completion is separate from host success | Existing scenario classifier remains authoritative | Named unit matrix rejects empty/host-only input; live suite checks actual captured serial |
| Seed warnings cannot be suppressed into capability admission | Existing version probe forces the warning | Behavioral shell shim replaces a brittle source-string assertion; this is capability-unit evidence only |

The two regression scenarios were authored before their production fixes.
No executable RED was observed: **RED TEST_BLOCKED**. No GREEN, branch
coverage, generated-manual or live-host PASS is claimed.

## Actual runner inventory

The existing Windows deployed executable at
`C:/Users/ormas/dev/simple/bin/release/x86_64-pc-windows-msvc/simple.exe`
has SHA-256 `6094dcae291aa984973ccd681f956e67a7a60543ab99f76a29313fbbfdee96d1`.
It has no adjacent provenance receipt and no corresponding receipt in the
canonical runtime-provenance hash index. It was not executed or modified.
Checked canonical full/Stage4 paths in the bootstrap repair worktree contained
no admitted runner. Root confirmed no newly admitted Linux runner: seed checks
had completed but canonical provenance hashing preceded Phase 2. The Windows
candidate failed sanity. This inventory, not the absence of a convenient
binary name, prevents an admissible test run.

## Resume once an actual runner is admitted

Preserve path/hash/source/provenance and exact executed-assertion counts. Run
each unchanged criterion once; at most three fix cycles per concrete failure.

```text
<runtime> test test/01_unit/os/qemu_cli_run_mode_v1_spec.spl --mode=interpreter
<runtime> test test/01_unit/os/qemu_named_guest_evidence_v1_spec.spl --mode=interpreter
<runtime> test test/01_unit/os/simpleos_compiler_admission_spec.spl --mode=interpreter
<runtime> test test/03_system/os/feature/qemu_catalog_dispatch_acceptance_spec.spl --mode=interpreter
<runtime> test test/03_system/os/feature/qemu_sealed_cli_route_acceptance_spec.spl --mode=interpreter
```

Run docgen and `sspec-maintain scan` for those five changed pairs, review actual
captures and require complete/zero-stub generation. The shell shim unit is not
native Windows acceptance. Run the real CLI/observer matrices separately on
Linux and Windows with actual prerequisites. Existing x86_32 executable-policy
refusal remains an explicit open boundary, not an inferred pass. The full
compiler/core/MCP gates are not claimed by this scoped OS source change.

The removal of a redundant cache shortcut means current provenance and input
checks run before reuse. Measure warm behavior when executable evidence is
available; do not replace current identity admission with an unqualified fast
path. Canonical build/native caches are retained.
