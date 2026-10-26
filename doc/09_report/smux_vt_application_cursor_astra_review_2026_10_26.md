# Smux VT application-cursor independent Astra review — 2026-10-26

**STATUS: WARN — source review only; execution NOT_RUN.** No blocking source
defect found in the seven pinned files. This is not verification PASS, merge
admission, generated-manual qualification or native keyboard compatibility.

Reviewer: independent Astra VT lane. Base HEAD:
`4b8a71f7d86549c9823e6e9b2b7dd8b2f25d522c`; worktree:
`D:/dev/simple-coremux-shared-20261025`. Review applied AGENTS.md, coding and
capability-interface guidance. Unrelated dirty paths were preserved.

## Findings and source evidence

- Constructor inventory across owned `src`/`test` found one `VtModes(...)`
  constructor; it explicitly initializes the new default-false scalar.
- Private mode one uses the existing local-copy/writeback path. Ordinary
  mode one and unknown private modes retain their existing behavior. The
  accessor is exported through `vt_screen` and reads the same live field as
  DECRQM. The parser retains `$` as an intermediate byte and dispatches only
  when final `p` arrives; fragmented set/reset similarly await `h`/`l`.
- RIS reconstructs default state. Reply clearing, SGR/OSC updates, resize and
  alternate-screen forms 47/1047/1049 preserve the scalar through existing
  value-state paths. No missing field reconstruction was found.
- Synchronized output freezes visual grids, not the input mode. Mode/query
  branches do not mark capture dirty; visual equality excludes mode state.
  Resize clears synchronization under existing policy while retaining mode.
- All ten authored cases call the production parser/accessor. Literal byte
  arrays, ordered reply strings, independent original/derived values and
  differing frozen/live text provide falsifiable oracles. No placeholder or
  tautological pass was found. The manual's complete fenced source matches
  the executable after newline normalization; its NOT_RUN label is accurate.
- `vt_screen.spl` is 754 lines, below the 800-line limit.

## Exact reviewed SHA-256 pins

| Path | SHA-256 |
|---|---|
| `src/os/apps/smux/vt_types.spl` | `fb090d6c67d038087f2af4737d4fcab48cb1ec00d4673f5f68041c48d3b22eb1` |
| `src/os/apps/smux/vt_screen.spl` | `f8e1d0fcb9b75cecef346be1455b3796913640c5cfcf3edb9efa1d82f1cb8702` |
| `src/os/apps/smux/vt_snapshot.spl` | `c6e530392054ab23f24628c1edc53354b42ccfe09990ec4db683d217d2f08a5c` |
| `test/01_unit/os/apps/smux/vt_application_cursor_spec.spl` | `9c1980edbbba7c2ba71fb9fb741d703568bac2bb473c6cabb400ffea995b2e7e` |
| `doc/06_spec/01_unit/os/apps/smux/vt_application_cursor_spec.md` | `4714ca300288e935fbf80f39efb3883a774da24820d9584387f268e638d088a5` |
| `doc/03_plan/sys_test/smux_vt_application_cursor_2026_10_26.md` | `de373279f35ec33685cc6b3d0bed3fce14b6bc340137b5d6bb3f6ca479a7c408` |
| `doc/09_report/smux_vt_application_cursor_source_2026_10_26.md` | `6ad56cdfa7ae42eb6ee146f3b38066ba39f38c1077c819792e52a347a4940f36` |

## Limits

Compilation, actual case execution, runtime value semantics, SPipe generation,
zero-stub admission and SSpec-maintain are NOT_RUN. Native PTY/ConPTY, SendKeys,
performance and coverage are unqualified. Existing parser behavior outside
this delta is not certified. No compiler/build/test/docgen process, staging,
commit or production edit occurred. No generator retry was consumed or reset.
Queue/I/O/facade, configured API/query and other moving lanes are excluded.
The context sandbox returned exit -1 without output; bounded PowerShell reads
were used. Findings were delivered to root and author before this report.
