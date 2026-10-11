# BUG-IT-1 — release/1.0 is not runnable by the deployed Windows seed (block-form `@when` decorators)

Date: 2026-10-10. Status: OPEN. Lane: stage2 intensive tests (work/rel-stage2-intensive-tests-20261010).

Symptom: `C:/dev/simple/bin/simple.exe {test,run} <anything>` from a release/1.0 checkout
fails in 1 s: `parse: in src/lib/nogc_sync_mut/io/windows_redirected_process.spl: Unexpected
token: expected Fn, found Colon`.

Cause: block-form conditional compilation `@when(os="windows"):` / `@else:` / `@end` (9 files on
release/1.0, landed 41d45e22c87 on 2026-10-02; 0 files on `main`). The deployed seed (sha256
e2a42543d62f, 2026-10-02 build, same bytes in every `C:/dev/simple-rel-*/bin/simple.exe`) parses
`@when(...)` only as a per-declaration decorator.

Reach: `std.io_runtime` -> `io.process_ops` -> `windows_redirected_process`; the compiler modules
import `std.io_runtime`, so even a compiler-only probe program fails identically. Nothing on the
line is seed-runnable; the only runnable binary is the stage2 bootstrap CLI (compile/native-build).

Workaround used by this lane: `C:/dev/simple-bootstrap-storage/seed-head/simple.exe` (sha256
278e9d1137..., 60.5 MB, built 2026-10-10 05:33) parses the block form and runs specs (`run` ~130 s,
`test` ~420 s per spec file). It is not deployed to any `bin/`.

Ask: deploy a seed that carries the block-form parser to the release lanes' `bin/simple.exe`, and
record in `.claude/rules/bootstrap.md` that release/1.0 requires a seed >= that build.
