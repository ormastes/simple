# Windows retained command owner V2

Status: **NOT_RUN**. Authored manual; no native execution, doc generation,
compiler, ABI link or allocation-failure qualification was performed.

Source: `test/01_unit/lib/io/windows_command_owner_v2_spec.spl`.

REQ-WINDOWS-COMMAND-001: bounded explicit launch fields, unambiguous environment,
exact argv and a real admission expiry are required before native effects.

REQ-WINDOWS-COMMAND-002: output bytes remain bytes until complete bounded capture;
invalid UTF8 is an explicit error, never invented decoded content.

| Pure production contract | Expected behavior |
|---|---|
| Absolute executable, cwd and explicit environment | Admitted request shape |
| PATH search or relative cwd | Rejected |
| NUL in executable or argv | Rejected before native conversion |
| Missing expiry, zero timeout or excessive capture bound | Rejected |
| Invalid or case-insensitive duplicate environment keys | Rejected |
| Deadline just before / exactly at expiry; unavailable clock | Admit / expire / refuse |
| Empty and spaced arguments | Preserve distinct argv through quoting |
| Successful resume at counter zero, boundary timeout, regressed counter | Enforce timeout / expire exactly / refuse regressed clock |
| Complete multibyte UTF8 / truncated bytes / empty bytes | Exact scalar / error / empty text |

The actual owner keeps one nonreused registry slot on the canonical Windows
thread. `begin` creates no child. `step` progresses preparation, inherited pipe
whitelist, kill-on-close JobObject, suspended create, assignment, deadline-gated
resume, writer closure, capture, termination and cleanup. Capture uses at most
4096 available bytes from each stream per step and zero-wait process polling.
Cleanup attempts one native handle or heap allocation release per step and
retains its exact owner on failure. Expiry gates admission; running timeout is
separate. Only actual signaled process plus empty assigned job permits cleanup.

Native happy-path, partial output pressure, timeout, expiry between create/resume,
cancellation at every stage, assignment failure, failed termination,
failed CloseHandle/HeapFree, same-thread rejection and copied-owner retirement
remain **UNQUALIFIED**. The nine pure cases do not execute native paths.
Pure decoder/admission cases do not establish those native properties. No
placeholder native scenario claims a pass.

Final UTF8 validation/decoding can process up to 16 MiB in its terminal turn;
that turn's latency remains unqualified.

The trust boundary matches the former Docker capture: explicit trusted absolute
executable and directory, without a shell or synchronous executable hashing.
This owner does not claim pinned executable identity or hostile-path containment.
