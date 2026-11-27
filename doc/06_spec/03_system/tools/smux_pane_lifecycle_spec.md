# Checked smux pane lifetime

Source: `test/03_system/tools/smux_pane_lifecycle_spec.spl`.
Requirements: REQ-CMUX-002/004/005/008/010.
Status: **WARN / NOT_RUN**. Eleven authored cases, zero executed. The coverage
annotation is a requested measurement target, not measured coverage.

The public bool `smux_close_pane` means true only after checked native teardown
and registry removal. False retains the pane and its native authority for retry.
While a multi-pane close is pending, that window rejects input, spawn, geometry,
focus and rollback mutation, and background polling preserves its records.
Other windows may continue. The exact target may retry; a different pane in the
same pending window cannot start competing closure.

Closing a final pane delegates to checked window removal and, for the final
window, checked session/attachment/lease/notification teardown. The full identity
is validated before delegation. A repeated last-pane request can continue that
same checked teardown even after its window/session closing flag is installed;
it cannot reopen a child or clear the flag as if cleanup succeeded. A full
window/session kill may supersede a pending pane-close intent only after it has
installed its own closing marker, preserving the original native handles.

| Case | Steps and required observation |
|---|---|
| Owned pipe refusal | Give the pure removal guard a record with retained process authority; require refusal and unchanged record/count. No native call is made. |
| Deferred PTY refusal | Give the pure guard a retained PTY handle with no PID; require refusal and exact handle retention. |
| Identity checks | Wrong session/window/pane combinations cannot close or add pending intent. |
| Geometry and focus | Remove a released focused record; retain survivor text, rectangle coordinates/size and next ID; choose surviving focus. |
| Pending exclusion | Pending-window and poll projections block that window; competing close preserves state and original intent. |
| Exact retry intent | A released target completes its own intent; unrelated window intent survives. This is state-transition proof, not forced native failure. |
| Final-pane guard | The lower owner refuses final-pane removal so the public checked window/session path owns lifetime. |
| Public close/checkpoints | Close a focused split pane; select survivor focus, invalidate only its window checkpoint, retain another window's valid rollback. |
| Last-pane ownership | Close one window's last pane then the final session pane; no empty live window/session or retained attachment remains. |
| Real piped child | Start two cmd.exe children, observe computed5859 and both OS PIDs present; close target, require target absent and survivor present with fresh3032; require both absent after checked cleanup. |
| Real ConPTY child | Repeat with actual ConPTY; require the same independent PID observations, checked cleanup and zero deferred PTY cleanup count. |

Cycle2 also updates three existing cases in the layout/protocol suites to
require final-window/session deletion and exact unknown-session replies, and
adds one independent pure empty-window layout guard. Those are separate from
the eleven cases above. Every case remains NOT_RUN.

## Actual native execution prerequisite

Use the canonical production SSpec runner built by an admitted Phase 3 producer,
with its real positive/negative framework preflights already satisfied. Select
`--native-backend llvm --library-mode nogc-sync-mut` and generic source roots
`src/providers/windows_native/lib`, `src/app`, `src/lib`, `src/os`, `src/compiler`.
Use current source hashes, matching linked runtime, private output/cache scope,
normal enforced 5,859,375 KiB process-tree cap and finite coordinator deadlines.
No seed/interpreter substitute, zero-case result or authored count is a PASS.

The native cases run only where real Windows cmd.exe/ConPTY is available. Their
internal output waits are at most80 polls with25ms sleep, and checked close/cleanup
retries have a5s monotonic admission deadline and200-attempt ceiling; individual
native close calls retain their provider's blocking bounds. The outer process
owner must still retain actual Job membership, terminal child/tree observation,
peak memory and cleanup receipts, including if the scenario crashes. A process
launch failure or missing provider is a failure/NOT_RUN, not an empty success.
The new `sosix_process_exists` is an exact alias to existing `process_exists`,
which calls `rt_process_exists` directly, without the other helper's `/bin/ps`
fallback. Both C `runtime_core_host_services.c` and Rust `env_process.rs` use
Windows `OpenProcess(PROCESS_QUERY_LIMITED_INFORMATION, PID)` and conservatively
treat access denied as existence. This is PID presence, not an exit-status or
owned-child registry query. The fixture
keeps both returned PIDs in its immediate owned-child scope and queries before
close, before full cleanup and after cleanup. PID queries are not creation-time
identity leases: PID reuse, retained process objects or query failure can make
observations ambiguous. The former `process_is_running` alias was removed:
some Windows providers interpret its argument as an owned handle or registry
key, so a numeric PID was not portable across admitted runtime choices. The
source contract of `process_exists` does not prove its linked provider; the
actual producer/runtime symbol and ABI binding must still be retained. Queries do
not prove descendant termination or Windows Job quiescence; terminal coordinator
receipts remain mandatory. Assertions run only after best-effort owned cleanup.

## Remaining real failure evidence

No production fault injection or fabricated native-close response was added.
The pure owned-handle cases do not prove `pty_close`/`process_close_piped` actually
returned false. Qualification still needs a controlled real deferred/failed-close
scenario: observe false, exact retained handle/record, unchanged geometry/focus,
blocked mutation and successful same-target retry after native cleanup completes.
Repeat for a final pane to prove retry passes the installed closing flag. Also
exercise escalation to window/session kill and confirm no child is orphaned.
Retain truthful failure if the provider cannot reproduce that condition safely;
do not count an always-successful close as this negative criterion. These cases
remain **NOT_RUN**, separately from the eleven authored executable cases.
