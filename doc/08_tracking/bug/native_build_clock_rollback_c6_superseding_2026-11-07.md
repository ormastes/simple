# Native-build rollback freshness: corrected C6 candidate, integration pending

Status: source repair prepared; full-driver and pure-tool qualification pending.

The Rust bootstrap driver's freshness floor compares an emitted artifact mtime
with a wall-clock build start. A real backwards clock step can make a newly
created output appear stale. The repair records one-use absence evidence for
the exact planned absolute output before building. Only an observed rollback,
an actual link and that exact consumed proof waive the mtime comparison.
Existence, nonempty output and existing code-content/functionless-ELF checks
remain in the original artifact validator. No clock or mtime is changed.

This source is the unchanged corrected C6 candidate from the retained clock
lane, SHA2566d1cdf93f8eb7869f0898e79c5bec1df41df8707b951699f640ae1899263cc67.
It supersedes the older C5 clock slice in unfinished PR7344 rather than importing
that32-path draft. C6 additionally anchors once and uses the same PathBuf for
proof comparison and metadata/content validation, preventing a process CWD
change from redirecting validation to another output. Current release99f has
the exact original owner blob554158e066241cc4dbde3db5bb8c748d2f4a63f6,
so only this one driver delta and this historical note are prepared.

Preserved history: C5 full driver10/10 passed in the merged32 context; that does
not qualify its later CWD repair. C6 criterion1 executed the exact production
helper extraction and11 real contracts:11 passed,0 failed,0 ignored. Existing
receipts remain unchanged in build/review/clock-freshness-cycle6. Do not replay
that green criterion, reset the six-cycle ledger, reclassify old failures or
claim a new execution budget because the source base changed.

A retained C6 full-driver criterion2 receipt was subsequently located at
build/review/clock-freshness-cycle6/integration/evidence/CLOCK6-INTEGRATION-RESULT.sdn
(SHA256 a0fd2392a3b334edc623950fb4c8239420c3a44f906faff5fb777688b034c448).
It records11 passed,0 failed,0 ignored, exit0, complete/quiescent1 and peak RSS
3739964KiB. Tested driver SHA2566d1cdf93f8eb7869f0898e79c5bec1df41df8707b951699f640ae1899263cc67
exactly equals this candidate. Its historical broader source context was53f,
not the current99f baseline: this qualifies owner-identical full-driver
integration, not the entire current source closure. No test was replayed.
Mandatory pure compiler/lib/MCP/LSP gates and applicable native smoke remain
pending. No build or tests ran for this99f source preparation. PR7479 remains
unfinished pending required review/checks; no merge or BugDB closure is claimed.

The11 contracts cover fresh output during rollback; preexisting stale output;
wrong-path proof use; ordinary-clock floor; cached/no-link behavior; missing
and empty outputs; metadata errors; relative-path anchoring; unchanged
functionless-ELF rejection; and a deterministic CWD-change negative control.
Tests must run single-threaded because the last test changes process CWD and
restores it through its fixture guard.

This narrower clock false-rejection case does not reopen or rewrite the older
pure-CLI staging history in native_build_stale_final_output_admission_2026-07-23.
That separate owner prevents stale-output false success and remains preserved.
