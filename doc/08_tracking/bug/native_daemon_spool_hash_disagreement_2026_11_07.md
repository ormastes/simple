# Native daemon spool path hash disagrees within one executable

Status: OPEN, report-only (not registered in bug_db). Proposed priority P1.
Group: compiler/runtime; attribution between lowering, inlining and runtime remains unproven.

Observed on aarch64 Linux using unadmitted pure-Simple compiler SHA256
`afae09d224390a57d675a128a052626c3aa665c032481928332ebdc2859d7350`.
Source base: `662c9c4fe01b07f3712faeccab945ee69fcd889c`, plus the daemon
publication regression fixture and envelope-admission guard in this PR.

Reproducer: `test/fixtures/daemon_sdk/publication_regression.spl`, selection
`success`. It uses the real request writer, runner and checked acknowledgement.
Expected: successful response publication removes the same request path.
Observed: response is published, acknowledgement attempts a different path,
and the success assertion fails. Do not weaken the expectation.

Syscall evidence from `build/daemon-publication-native/deletion.trace`:
- Request write/rename: `requests/0_3875265_1794017034495863.req`.
- Response write/rename: `responses/3875265_1794017034495863.resp`.
- Acknowledgement unlink: `requests/-8547548619830576675_3875265_1794017034495863.req` returns `ENOENT`.

All request paths use `daemon_request_path_for`, which calls `hash_text`.
The same request identity must hash consistently at writer, reader and cleanup
call sites. The trace establishes disagreement; it does not prove which
compiler or runtime function caused it. No compiler repair was attempted.

Related historical symptom: [cross-lane hash disagreement](rt_hash_text_cross_lane_disagreement_2026-09-07.md).
That report concerns older lanes and remains historical evidence; this is a
fresh within-executable observation, not proof its original cause returned.

Build: LLVM, `core-c-bootstrap`, entry closure, one thread,
`SIMPLE_NO_STUB_FALLBACK=1`; build exited 0, fixture exited 1.
The diagnostic compiler is not admitted. Admitted SSpec and runtime gates are
BLOCKED; this report does not certify a production regression or a repair.
