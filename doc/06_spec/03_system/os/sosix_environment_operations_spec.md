# Hosted SOSIX environment operations

Audience: tool authors using `std.nogc_async_mut.sosix.environment` and reviewers
checking which operations were exercised on this host.

## Evidence and qualification

At release source `17c632ff6a01b0950740cb680604ca251ed2b2f6`, diagnostic execution
on macOS arm64 produced **11 passing examples, 0 failures, 4 planned cases**:
unit admission 2 pass / 2 planned; V4 request schema 4 pass; system operations 5 pass / 2 planned.
These are **Rust P1 interpreter diagnostics**, not native Simple, Windows,
Linux, FreeBSD, illumos/Solaris or SimpleOS guest provider qualification. No P2
rebuild was performed. The existing native binary reports `Simple v1.0.0-beta`;
its version output alone was not used as execution evidence.

Binary: `/Users/ormastes/simple/src/compiler_rust/target/bootstrap/simple`.
SHA-256: `59de8c475ac8e364ebbd082d080e435a7aaffb4606d8fbc276a5372dcb3f87e6`.
Each spec was run from the isolated release worktree with:

```sh
<diagnostic-p1> test <relative-spec-path> --mode=interpreter --no-cache --no-db --no-session-daemon --sequential --assert-ran
```

The logs retain seed warnings and cross-module/layer diagnostics. File verdicts
include explicit skipped counts, while the runner's final `Results` summary
counts only nonpending examples:
[admission log](sosix_environment_operations_evidence_20261029/admission.txt),
[operations log](sosix_environment_operations_evidence_20261029/operations.txt),
[V4 request log](sosix_environment_operations_evidence_20261029/v4_environment_request.txt).

## Admission scenarios

Executable source:
`test/01_unit/lib/nogc_async_mut/sosix/environment_admission_spec.spl`.

1. Submit empty and equals-containing names to lookup, assignment and removal.
   Checked results reject them; bool mutators return false.
2. Submit NUL-containing names and values. Admission rejects them before the
   provider can truncate input.
3. Present malformed UTF-8 keys and values. The assertions demand typed codec
   failures with byte offset one. On this P1, `rt_bytes_to_text` converts invalid
   bytes with `String::from_utf8_lossy`, so these fixtures are explicitly planned
   as unsupported. The source lives at
   `src/compiler_rust/compiler/src/interpreter_extern/conversion.rs:195`.
   A raw-byte-preserving provider runs these assertions. No codec rejection
   qualification is inferred from rewritten valid replacement text.

## V4 architecture boundary

Executable source:
`test/01_unit/lib/common/process_observation_environment_v4_spec.spl`.
Four pure production-schema scenarios exercise `ProcessObservationRequestV4`
and its canonical codec: exact empty/Unicode values, explicit empty environment,
sorted unique keys, and invalid key/value refusal. Request pin claims are shape
fixtures only, never live capabilities and never submitted to a provider.

V4 uses an **explicit environment list bound into the canonical request**.
The hosted environment facade changes the parent process environment. The
bounded SOSIX compatibility capture used below observes parent inheritance;
it does not submit a V4 request or prove V4 environment isolation. Native V4
child environment delivery requires an admitted matching provider, live
executable/cwd pins, and frozen receipt evidence; none is inferred from these
P1 diagnostics. No V3 or path-spawn fallback substitutes for that admission.

## Environment lifecycle scenarios

Executable source:
`test/03_system/os/sosix_environment_operations_spec.spl`.

| Scenario | Expected result | macOS P1 |
|---|---|---|
| Remove then set empty | Checked/nullable preserve nil versus Some(""); default-text returns empty for both; filtered-opt returns nil for both. | PASS |
| Set and replace Unicode key/value | Exact text survives both assignments; removal clears it; repeated removal succeeds. | PASS |
| Replace existing value with embedded NUL | Checked assignment fails; old value is retained. | PASS |
| Read cwd | Checked result is nonempty with no NUL. | PASS |
| POSIX child inheritance/isolation | Bounded `/bin/sh` child prints exact inherited Unicode value, child export leaves parent unchanged, subsequent child sees unset after parent removal. | PASS |
| Windows case-insensitive lookup | Alternate key spelling reads assigned value. | PLANNED: matching Windows host required |
| Windows cmd inheritance/isolation | `cmd.exe` inherits parent value; child mutation stays local; fresh child sees absence after removal. | PLANNED: matching Windows host required |

Scenarios save and restore dedicated keys before checking captured observations.
No host PATH/HOME/locale variables are modified. Child execution has a 5-second
timeout and 1024-byte capture bound; child stdout is placed in an in-memory authored text evidence value and checked
against exact expected content. `scenario_evidence_artifact` constructs a value;
it does not register or persist a separate child-output artifact. The retained
run logs contain the scenario verdicts, not a standalone emitted capture. Host-specific scenarios
are declared planned on nonmatching hosts. Lifecycle scenarios similarly refuse
to run when SOSIX does not admit the host environment provider.

## Uncovered operations

There is no SOSIX ordinary snapshot/list export in this module. Raw
`rt_env_vars` and `std.io.env_vars` are different routes and are not claimed.
The API has checked cwd lookup but no SOSIX cwd setter here. Live V4 explicit-environment delivery, clear-environment launch behavior and
SimpleOS guest inheritance remain outside this diagnostic execution evidence;
only their V4 request representation is covered here. Allocation-failure versus missing
lookup cannot be distinguished by its underlying nullable provider.
