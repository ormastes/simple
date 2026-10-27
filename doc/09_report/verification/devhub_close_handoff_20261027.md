# DevHub session close handoff

The user requested canonical bug/TODO registration, landing eligible work, and closing this session. Feature experiments stopped. The secured Messenger database is not fixed.

## Preserved work

- Independent DevHub fixes: PR [5085](https://github.com/ormastes/simple/pull/5085), branch `fix/devhub-completion-20261027`.
- Raw registry fixtures now retain their intentional bytes across Windows/Linux checkout (`abb16238d22`). No CRC gate exemption was added.
- Real mail SDN helper provisioning is saved as WIP (`5eb7aa40ee8`). Focused tests using the existing real Windows helper passed, as did four provisioning admission tests. Qualified host producer profiles are missing, so the hosted matrix is not qualified and provisioning fails closed.
- Secured DB branch `fix/devhub-secured-db-p2-20261027` is pushed. It preserves callback/cleanup changes, a fresh acceptance fixture, an unreferenced/unrun snapshot candidate, and a detailed failure report at `doc/09_report/verification/devhub_secured_db_session_close_20261027.md`.

## Actual blocker and landing status

The fresh secured-DB native build succeeded using the unchanged pinned phase-2 compiler. Its native run exited 1 when direct key-session opening returned `Err`, before decoding, registry dispatch, or Messenger rows. The old RTS01 panic was not observed in this run; its repair is not proven. The independent fixture oracle passed and encrypted source bytes/metadata remained unchanged. No second fresh attempt was started.

Automatic self-review admission rejected PR #5085 at head `6c067bee4725f1d05c5ab1311b300b9f92bda31b`: `immutable semantic restriction matched current content: credential_secret` (check `122061116596`). No bypass or repeated admission is attempted. Landing requires policy-owner resolution and ordinary current-head checks; pushing saved commits does not constitute a merge. The original hosted mail fixture and CRC failures are retained as evidence, with subsequent repairs/WIP distinguished from hosted PASS.

Remaining DB work includes isolating the typed key-session failure, real rooms/members/history/fetch acceptance, native snapshot qualification, journal/WAL support policy, session reuse and bounded paging/row traversal. Do not claim full security cleanup, efficient database access, formal SSpec execution, all configuration families, or live account qualification.
