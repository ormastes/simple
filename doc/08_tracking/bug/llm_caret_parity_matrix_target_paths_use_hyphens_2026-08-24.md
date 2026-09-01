# LLM Caret parity matrices point at hyphenated `.spl` targets that repo convention forbids

- **Date:** 2026-08-24
- **Status:** OPEN
- **Component:** `doc/03_plan/trace/llm_caret_claude_cli_full_parity_{file,symbol}_matrix.tsv`,
  `scripts/check/check-llm-caret-full-parity-implementation.shs`
- **Severity:** medium (gate reports work as unimplemented when it is implemented)

## Symptom

`sh scripts/check/check-llm-caret-full-parity-implementation.shs` reports
`class_target_files_missing=15` and names, among others,
`ink/events/click-event.ts:10 ClickEvent target=src/app/llm_caret/claude_full/ink/events/click-event.spl`.

## What is actually true

All 15 "missing" classes are already ported and present. The checker's target
column carries the TypeScript basename verbatim (hyphens, and `native-ts/`),
while the Simple ports live at the snake_case paths repo convention requires:

| matrix target (does not exist) | real port (exists) | class |
|---|---|---|
| `ink/events/click-event.spl` | `ink/events/click_event.spl` | `ClickEvent` |
| `ink/events/focus-event.spl` | `ink/events/focus_event.spl` | `FocusEvent` |
| `ink/events/input-event.spl` | `ink/events/input_event.spl` | `InputEvent` |
| `ink/events/keyboard-event.spl` | `ink/events/keyboard_event.spl` | `KeyboardEvent` |
| `ink/events/terminal-event.spl` | `ink/events/terminal_event.spl` | `TerminalEvent` |
| `ink/events/terminal-focus-event.spl` | `ink/events/terminal_focus_event.spl` | `TerminalFocusEvent` |
| `ink/log-update.spl` | `ink/log_update.spl` | `LogUpdate` (:43), `VirtualScreen` (:752) |
| `ink/terminal-querier.spl` | `ink/terminal_querier.spl` | `TerminalQuerier` (:128) |
| `commands/remote-setup/api.spl` | `commands/remote_setup/api.spl` | `RedactedGithubToken` |
| `native-ts/color-diff/index.spl` | `native_ts/color_diff/index.spl` | `ColorDiff`, `ColorFile` |
| `native-ts/file-index/index.spl` | `native_ts/file_index/index.spl` | `FileIndex` |
| `native-ts/yoga-layout/index.spl` | `native_ts/yoga_layout/index.spl` | `Node` |
| `services/oauth/auth-code-listener.spl` | `services/oauth/auth_code_listener.spl` | `AuthCodeListener` |

Every listed class was verified present at the snake_case path, and the source
line numbers recorded in the symbol matrix match the ported files exactly
(`log_update.spl:43 LogUpdate`, `log_update.spl:752 VirtualScreen`), so these
are the intended ports, not coincidental name collisions.

The same defect affects the file matrix, but only partly:

```
missing=1256  of which a snake_case sibling exists=101  exists=646
```

So 101 of the 1256 "missing file" rows are the same naming artifact; the
remaining ~1155 are genuinely unimplemented and the gate is right about those.

## Impact

`class_target_files_missing` can never reach 0 by writing code, and the file
side over-reports the remaining work by 101 rows. The only honest ways to make
the gate green are outside a porting session's scope: regenerate the matrices
with the target basename snake_cased, or teach the generator to apply the
repo's module-naming convention when it derives a `.spl` target.

## Recommended fix

In whatever generates `doc/03_plan/trace/llm_caret_claude_cli_full_parity_*.tsv`,
snake_case the derived `.spl` target path (`-` -> `_`) for both the file and the
symbol matrix, then regenerate. Do not create hyphenated shim `.spl` files to
satisfy the gate — that would plant convention-violating decoys.

## Secondary blocker

`tmp/claude/claude-code-main/src/` — the TypeScript source tree the matrices are
derived from — is not present in this worktree, so no row can currently be
re-derived or a port re-checked against its source. Any lane that intends to
continue this port needs that tree restored first.

## Work landed alongside this record

Behavioral unit specs for the ink terminal-event cluster (the ports were
verified real, not stubs), under
`test/01_unit/app/llm_caret/claude_full/ink/`.
