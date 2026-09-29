# Stage3 Windows process inventory rejects BSD ps options

## Failure

The real MSYS `ps -ax -o pid= -o ppid= -o rss= -o args=` probe exited 1 with `unknown option -- x`. `scripts/check/lib/bootstrap-stage3/memory-admission.shs` therefore records the process scan as unavailable. The existing exclusive-heavy gate correctly refuses unavailable inventory (exit75), preventing Stage3 resume. An unavailable inventory must not be converted to an idle host.

## Correction

On MINGW/MSYS/CYGWIN, query native `Win32_Process` through CIM instead of BSD `ps`. The provider serializes the existing `pid|ppid|rss_kib|command` contract, sorts by PID, validates numeric/image data, sanitizes separators/newlines, and rejects partial snapshots above 16384 rows or16MiB. Missing command lines on gate-sensitive compiler/interpreter/QEMU images fail the query; protected ordinary system/service rows retain their image name. Native `simple.exe` argv identity is normalized for the existing classifier, including quoted Windows paths. The classifier, exclusive-heavy gate and Linux/BSD/Darwin `ps` path remain unchanged.

The native query owns one temporary result file and a hidden query worker. CIM has a10s operation bound, and its parent waits15s for the complete operation, then stops only its owned worker and waits at most5s for reaping. No unrelated process is signaled. Provider failures remain unavailable and gate refusal.

## Verification plan and scope

`scripts/check/check-bootstrap-stage3-windows-process-inventory.ps1` checks a real CIM snapshot against the live test owner's PID/PPID/nonzero RSS. It starts real owned sleeping Windows processes with explicit classifier-control argv labels, observes their actual CIM rows, and runs the existing admission gate to require busy/unavailable exit75. These controls do not pretend to run a compiler or bootstrap. Snapshot/result files remain in the specified D evidence directory; only owned controls are cleaned up.

## Focused execution

Windows cycle1 passed on2026-09-29:401 actual CIM rows, live test-owner PID9148 present exactly once, correct PPID and nonzero RSS. All four owned classifier-control PIDs were observed by the production scan. The actual exclusive-heavy gate refused busy inventory (native1/bootstrap6/QEMU1) with exit75, and refused unavailable inventory with exit75. Evidence: `build/recovery/windows-inventory-cycle1/{result.env,native.snapshot,busy.env,busy-gate.stdout,busy-gate.stderr}` in this isolated checkout.

One default Linux check passed under Ubuntu22.04 WSL: the production scan selected `ps` and recorded available inventory; the existing fixture contract retained native1/bootstrap2/QEMU1 and busy refusal75. Evidence: `build/recovery/linux-inventory-cycle1/{result.env,real.env,busy.env,check-linux-contract.sh}`. The passing checks are not repeated.

No Stage3/Phase4 PASS is claimed. This change preserves the existing Win32 Job/RSS enforcement; it does not claim native Windows8GiB virtual-memory enforcement or waive a guard. Prepared separately from the frozen live5da checkout on GitHub main `bb3f6ab8ab29233fcc28f1fd4c239fe86aab8bf9`.

## Executable-input authority review

The new PowerShell provider is an executable input. The existing facade helper-bundle snapshot (`scripts/check/lib/bootstrap-stage3-provenance.shs`) binds seven roles: facade, authority, command, sanity, manifest_write, manifest_verify and self_test. It does not currently include either the separately sourced memory-admission helper or this new provider. Stage3 resume records source/Git state before execution (`resume-stage3-from-admitted.sh:659–660`) and the resulting manifest retains `git_head`; freshly hashing a mutable companion file alone would not prove authorization.

The provider capture derives the canonical Git root from the actual sourced facade, requires its recorded directory and Git root to match, pins HEAD and the provider blob, and checks `git cat-file` before executing a private captured `.ps1`. Both the live source (Git-normalized text) and captured bytes must match the committed blob before and after execution; HEAD must remain pinned. Missing committed input, changed source, changed captured bytes, or a changed root/HEAD fail inventory closed. Root, commit and blob identifiers are included in the existing process-scan evidence without extending the seven-role helper protocol.

The binding-only check exercises committed execution plus five refusal controls in a private real Git repository; it does not modify the production checkout or create a bootstrap-admission receipt. Binding execution is pending the local commit needed to provide genuine committed authority. Cycle1 proves the reviewed provider/gate behavior; final Stage3 qualification remains pending.
