# Secure Pure-Simple servers: evidence status

Date: 2026-08-14

## Temporary staged-runtime provenance

The strongest current-source staged artifact found in this worktree is
`build/bootstrap/stage2/x86_64-unknown-linux-gnu/simple`:

- SHA-256: `5883722a6cafd17006ecab001e714e9e43774014bf44b1af459a92bd142099f5`
- ELF Build ID: `9db2d66edbf77fc3fd0674f3cc21ae4062a2b6ec`
- Size: 131,026,208 bytes; version: `simple-bootstrap 1.0.0-beta`
- Producer receipt:
  `build/bootstrap/stage3/x86_64-unknown-linux-gnu/stage2-command.transcript`
  records LLVM with `core-c-bootstrap`, `SIMPLE_BOOTSTRAP=1`,
  `SIMPLE_NO_STUB_FALLBACK=1`, and entry `src/app/cli/bootstrap_main.spl`.

This is a self-hosted Stage-2 bootstrap compiler, not an admitted Stage-4 full
CLI. An unverified operator observation says one `check` and one focused web
`test` probe returned `unknown command`. The artifact is retained as provenance
and that observation as a diagnostic negative only; neither can
credit a requirement, SPipe execution, docgen, or release gate.

Unverified operator observations say one bounded Stage-2 `native-build` was
attempted for each focused lane. The web
spec stopped in HIR (`ANY` field `error?` could not be inferred); the DB spec
reached link and lacked `core-c-bootstrap` symbols `rt_file_create_excl`,
`rt_file_sync`, and `rt_crc32_text`. Neither produced an executable, and no
variant was retried.

Unverified operator observations from the explicitly authorized bootstrap-seed
diagnostic then ran the DB specs
(seed SHA-256
`c9321d38fa7623008e185289bc9dc193489ab490f7ec238b9a3cadcd0b4788ea`):
durability 22/0. After bounded test-only corrections, secure server reached 7/0
and tier server ended 39/1; its remaining RED is UTF-8 batch round-trip (`猫`
became replacement characters), and the three-attempt cap is exhausted. These
commands have no retained immutable command receipts, so no acceptance credit
is taken and the symptom is unresolved: it is not attributable between the
seed/runtime and server implementation. This seed evidence is bootstrap diagnostics, never production or
admitted Stage-4 verification.

Sibling `restart12-*` worktrees expose the same deployed wrapper hash
`714e1e8e43474413b8c0b82cb561bc8585462e3539417e2c8dd883ea470fc736`
and the same `simple_native` hash
`7fc570189e1d689c8c99988981a4766b0a42ba9a70dc97571c71d2a75c46823b`;
they are not stronger independent candidates. No sibling staged artifact with
a full verification command surface was found.

## Authored, statically reviewable evidence

- `secure_pure_simple_db_server_spec.spl` calls the production `listen` entry
  point only for deterministic pre-bind rejection of zero connection capacity,
  then asserts listener/connection state remains released.
- `db_durability_spec.spl` covers the P3/P4 crash boundary and a reconnect retry
  using a durable, principal-bound commit receipt. Cross-principal and
  different-content reuse are explicit conflicts.
- DB capability coverage includes read-only, empty-grant, wrong-table,
  missing-table, write-only, and data-operation denial cases.
- Missing, wrong, and unknown credentials are checked against one exact
  `ERR code=auth msg=authentication failed` frame.
- The tier spec source contains an injected isolation violation plus
  unconditional controls, so static review finds a non-placeholder oracle;
  deliberate-red execution remains uncredited.
- Mirrored manuals exist for all three DB system specs.

## Release-blocking evidence not available

No admitted Pure-Simple Stage-4 CLI is healthy. Consequently no admitted
Stage-4 runtime executed or credited the DB specs or live-listener scenario,
and this lane did not run `sspec-maintain scan` or `spipe-docgen`; it did not
produce a genuine deliberate-red failure/restoration
transcript, runtime coverage, socket transcript, or `0 stubs` generator
receipt. Hand-authored manuals are not represented as generated provenance.

A live listener PASS is intentionally absent. A trustworthy scenario needs a
concurrent client/stop fixture that binds an assigned loopback port, connects,
exchanges messages, closes, and joins the listener owner. Calling `listen` with
no connector can hang when accept polls for shutdown; accepting any bind error
would be a vacuous oracle. Until that fixture and the runtime are admitted, the
real bind/accept/EOF/stop row is RED/BLOCKED, not skipped or passed.

Production and scripted drains now share `bounded_message_response`, and the
focused source scenario constructs an oversized encoded result. Runtime TCP
wire evidence remains RED/BLOCKED; structural sharing is not a socket transcript.

AC-9, AC-10, AC-12, and final-review AC-13 remain open. Production TLS remains
separately blocked by GAP-TLS-3. Static source shape cannot prove actual socket
accept/cleanup, scheduler exclusion across P3/P4, fsync/rename crash behavior,
or lost-ack replay behavior; those require the healthy admitted runtime.
