# MCP T32 exported state needs explicit native declaration visibility

Status: focused native before/after verified; SSpec and broad MCP execution pending. New independent feature
attempt counter: 3. The planner's six exhausted attempts remain unchanged.

The live full CLI qualification rejected imports of MCP_T32_AREA_NAME,
MCP_T32_CURRENT_CORE and MCP_T32_SESSIONS as non-public module statics.
The state owner explicitly exports all six state names. Its logical path is
`src/app/mcp_t32/session_state.spl`; the tracked source resolves through the
repository link to `examples/10_tooling/trace32_tools/t32_mcp/session_state.spl`.

The repair adds `pub` to exactly those six existing exported `var`
declarations. Names, types, initializers, export lists and callers are unchanged.
No private state is newly added to the API and no owner API redesign is made.
This follows the native evidence in
`scv_exported_static_native_visibility_2026_10_29.md`: explicit same-owner
export and declaration visibility currently remain separate during lowering.
The general export-list-to-native-visibility gap remains OPEN. Neither the
Cranelift refusal nor runtime visibility checks are weakened.

## Focused verification plan

`test/fixtures/bootstrap/mcp_t32_exported_state/` contains a native entry and
separate writer/reader modules importing the real state owner. It checks all
six initial values, writes all six through the writer, reads them through the
reader, then resets and reads again: eighteen named predicates. Real session
and history objects are allocated, but no TRACE32 process, device, protocol,
network or tool-dispatch function is invoked.

Use the pinned Hello-qualified ffe83fd producer and its matching runtime with
canonical enforcing guards, explicit Cranelift and private frontend/HIR/native
and temporary paths. First collect the unchanged-declaration native failure,
then the exact six-modifier repair with the same fixture. Preserve each source
snapshot and terminal receipt. Show source/probe plan to root before launch.
The separate SSpec has six real imported-state assertions and restores saved
state; its manual accurately marks it unexecuted. Broad MCP native/runtime
and qualified-CLI gates remain pending. No Phase 3 admission is claimed.

Attempt 1 preserved at `build/mcp-t32-exported-state/before1/` stopped at
`SCV-E-ADMISSION: source-inventory-root-not-git`; exit 1, quiescent 1,
peak RSS 55,432 KiB. Its four-file source snapshot was not an independently
committed Git root. No code compilation or assertions ran. The admission check
remains enabled; the proposed correction is to commit each tiny snapshot,
retaining this refusal and counting subsequent attempts separately.

## Executed native comparison

All paths below are relative to the isolated worktree
`/home/yoon/dev/simple-bootstrap-advice-plan-review-20261106/` on topic
`work/mcp-t32-exported-state-20261106`. This reused a clean, quiescent review
worktree; the planner branches, immutable evidence and exhausted counter remain
untouched. Producer SHA256 is
`ffe83fd87c69573a1ca93e24134e46bbe754be7dff2de2f0eeefc4cf60c9037a`, using its
matching runtime capsule, explicit Cranelift and canonical enforcing 24 GiB
process-tree guard. The standalone snapshots are local-only Git repositories;
no remotes were configured. Each tracks exactly the actual owner plus three
fixture files; `source-sha256.txt` binds those four bytestrings.

Attempt 2 (`build/mcp-t32-exported-state/before2/`), source commit
`e47d0a11da09b14e3def55724c2e29068826fddd`, retained the original plain declarations.
It reproduced the non-public `app_mcp_t32_session_state__MCP_T32_AREA_NAME`
static rejection in both real reader and writer modules: build exit 1,
quiescent 1; no executable assertions. Its copied source root also contained
untracked `.simple/` and `build/` artifacts generated during attempt 1.
Preparation flagged that caveat, but the shell continued into the build; this
attempt is counted and its root is not claimed pristine. The four committed
source files and original production hashes remain bound explicitly in its
`source-admission.sdn` and hash manifest.

Attempt 3 (`build/mcp-t32-exported-state/after3/`) copied only the four source
files and committed them as `85e5bce8d903ca5deded7e37d3b55c5e3f923d54`.
The root was clean before build; subsequent four-file hash and tracked-source
checks passed before execution. Preparation used fail-fast execution so a
failed assertion could not launch its dependent compiler. Build exit 0,
quiescent 1, peak RSS 833,952 KiB. Run exit 0, quiescent 1, peak RSS 8,844 KiB;
actual output was `ASSERTIONS=18 FAILURES=0`, with every named predicate printed
PASS across default, populated and reset states. Executable SHA256:
`dce39617ce453d77d78558a3677aaae3042c45cd9aaa57f132ff4951f5d8920b`.
Build/run scripts, logs, guards and source-admission records are retained.
Total focused artifacts occupied 2.2 MiB when measured; no unrelated cache or
other owner's data was deleted.

This proves real cross-module sharing of these six already exported state
values with explicit declaration visibility. It does not fix the general
same-owner export lowering gap, qualify TRACE32 connectivity, execute the
SSpec runner, or satisfy broad MCP/Phase 3 admission gates. No TRACE32,
network or device operation was invoked. No passing native check is repeated.
