# Smux VT application-cursor source lane — 2026-10-26

Status: **SOURCE IMPLEMENTED / AUTHORED TESTS NOT_RUN / QUALIFICATION BLOCKED**.
Base inspected: `4b8a71f7d86549c9823e6e9b2b7dd8b2f25d522c`, shared worktree
`D:/dev/simple-coremux-shared-20261025`. Other sessions' dirty files are excluded
and preserved. Parent approval covered exactly the seven paths below.

| Path | Change |
|---|---|
| `src/os/apps/smux/vt_types.spl` | Default-false live `application_cursor` scalar |
| `src/os/apps/smux/vt_screen.spl` | Explicit constructor initialization; private-mode one set/reset/query; canonical accessor export |
| `src/os/apps/smux/vt_snapshot.spl` | `vt_application_cursor(screen: VtScreen) -> bool` reads current live state |
| `test/01_unit/os/apps/smux/vt_application_cursor_spec.spl` | Ten production-parser SSpec scenarios, authored NOT_RUN |
| `doc/06_spec/01_unit/os/apps/smux/vt_application_cursor_spec.md` | Manual source mirror; no generator/execution claim |
| `doc/03_plan/sys_test/smux_vt_application_cursor_2026_10_26.md` | Contract, traceability, deferred admission and exclusions |
| `doc/09_report/smux_vt_application_cursor_source_2026_10_26.md` | This bounded source handoff |

The existing RIS constructor resets the new field. Existing value copies,
resize and alternate-screen paths preserve mode state; synchronized output
freezes only visual content. The accessor and DECRQM read the same live field.
Mode/query changes do not mark visual content dirty. No changes were required
to capture/history owners, frozen visual state, historical pins, raw-input
queues/facades, configured APIs or client protocol.

The constructor search found one production `VtModes` constructor, now explicit
about the false default. Existing adjacent structs demonstrate default-valued
boolean fields; language acceptance remains unexecuted. Source review and Git
whitespace checking are narrower than compiler, SSpec or backend validation.
The single scoped `git diff --check` completed successfully. Final source hashes
and line counts are sent to the root for independent review without modifying
historical evidence pins.

No compiler/build/test/docgen executable, native fixture, staging, commit or
publication ran in this lane. The parent restricted execution because runtime
explicit-library-mode qualification is blocked and the generator retry budget
requires an exception. No retry counter was reset. The context-mode batch reader
returned exit -1 with no file output, so bounded PowerShell file reads were used.

Independent review is pending with the root. Ten authored cases cover default
state, fragmented set/reset/query, exact reply bytes, unrelated modes, RIS,
copy/reply isolation, resize, all supported alternate forms, synchronized live
mode and visual-dirtiness separation. No native compatibility, SendKeys support,
coverage percentage, performance target, full verification PASS or release
qualification is claimed. This is a source dependency for later key encoding.
