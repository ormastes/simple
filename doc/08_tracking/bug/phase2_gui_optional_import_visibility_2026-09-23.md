# GUI markdown receiver type visibility after receiver metadata repair

Status: focused native regression PASS; combined Phase2 full CLI pending.

Base source: `e52ef0cc249d2e49b4d9d66070edd37ce269b4cc`, receiver PR #1380.
The admitted Stage2 SHA256 is
`98cbcdb15be2d04223bc03dd6ace3982b9e7826fbca9ec76e83a096f7a437cf3`.
The Phase2 full CLI build still fails in `src/app/editor/gui_shell.spl` with
`HIR Cannot infer field type: struct 'ANY' field 'preview_visible'`.
Authoritative evidence is under
`/Users/ormastes/simple-tmp/macos-phase2-receiver-admission-20260923/build/evidence/phase2-receiver-stage2-capacity-retry/logs/compiler_cli_build.log`.

The renderer lacked explicit imports of `EditorController`, `EditorDocument`,
and `MarkdownState`. Both GUI renderer modules now import those owners.
`EditorDocument` also names an unrelated three-field multi-buffer structure;
`preview_visible` and `outline_visible` occur at different field offsets on
several markdown structures. A global ANY-field fallback cannot safely replace
the declared receiver type.

This was missing owner type visibility, not unsupported optional projection grammar.
The hosted HIR boundary resolves `T?` to a pointer to T and recursively unwraps
that pointer during field lookup (`hir/lower/type_resolver.rs`). Therefore the
verified fix adds only six import lines, keeping the original nil guards and
nested field expressions. No annotation or `if val` rewrite was introduced.

The production regression fixture is byte-identical to the receiver lane's
accepted GUI fixture (SHA256
`1a5a995956da620b82438f15cf4cec82fdbb2e20cb79f2b516d6118186c66e08`).
It checks no document, absent state, hidden panels, populated preview,
preview-over-outline priority, populated outline, and problems-panel priority.
Native input hashes, field-resolution traces, elapsed time, sampled process-tree
RSS, and quiescent receipts accompany each run under
`/Users/ormastes/simple-tmp/phase2-gui-optional-admitted-20260923/build/evidence/gui-optional`.
The old three-cycle candidate and crash evidence remain preserved unchanged
in `/Users/ormastes/simple-tmp/phase2-gui-preview-20260923`.

## Results

| Target | Result | Build elapsed | Sampled build peak RSS |
|---|---|---|---|
| Baseline, unchanged e52 source | Expected failure: ANY.preview_visible | 10.95 s | 206,288 KiB |
| Legacy gui_shell, imports only | 141 compiled, 0 cached/failed; 7/7 behavior cases | 15.19 s | 334,960 KiB |
| Split gui_shell_core + gui_shell_render | 142 compiled, 0 cached/failed; 7/7 behavior cases | 14.17 s | 348,656 KiB |

Both native runs exited 0 and printed `gui-markdown-optional-frame: PASS cases=7`.
Run elapsed times were 0.37 s and 0.34 s; Darwin `time -l` measured
10,338,304 bytes maximum RSS for each. The 100 ms process-tree samples observed
only 2,560/2,384 KiB during these short runs; those sampled values are not
substitutes for the Darwin peak measurement. All build/run receipts report
`quiescent=1` and sampled enforcement under a 5,859,375 KiB cap;
`hard_memory_limit=0` means no kernel hard containment claim.

The baseline trace uses ANY/global lookup for md_state before failing.
Both green traces have no ANY fallback for session, md_state, preview_visible,
or outline_visible in the edited renderer. The split renderer still resolves
its ambient GuiShellState.ctrl through the global field table at index 0;
this separate existing type-visibility surface is not claimed repaired.
There are no runtime control-flow, allocation, FFI, or platform dependency
changes. Timing proves bounded focused execution, not a performance speedup.

The split evidence entry is the exact regression body with only
`use app.editor.gui_shell.*` replaced by imports of `gui_shell_core.*` and
`gui_shell_render.*`; its bytes and input hashes are retained alongside
`run-focused.shs`. Native commands select the pinned admitted compiler and
verified runtime capsule, `--source src/app --source src/lib --entry-closure`,
`--threads 1`, isolated caches, and `SIMPLE_NO_STUB_FALLBACK=1`.
The source baseline and both owner projections consumed three scoped cycles.

Whitespace and working direct-env-runtime guards passed; executable specs under
doc/06_spec count 0. Independent Astra review accepts the scoped source fix and
native regression. This is not full CLI, full compiler-suite, Stage3, or release
acceptance; those gates remain with the bootstrap owner.
