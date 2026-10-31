# DevHub secured Messenger DB key-session open failure

Status: OPEN. Severity: P1. Date: 2026-10-27.

The fresh secured DB ledger1 build passed with the existing Phase2 compiler, but actual execution failed at direct key-session open before encrypted decode. The memory oracle passed NIST AES, independent KDF/HMAC, SQLite integrity, rows and overflow checks. The encrypted inputs and metadata stayed unchanged and no plaintext or journal secret files remained.

This is the main DevHub Messenger database feature blocker, not an infrastructure exemption. The exact cause remains unisolated. Repair key-session open first; then qualify secure SQLite decode, snapshot lifetime and efficient bounded paging with independent row oracles and memory-only plaintext. Do not claim DB support from the memory oracle alone.

Evidence: `D:/dev/simple-devhub-secured-db-p2-20261027/build/devhub-completion/fresh-secured-db-ledger1-build.log` and `fresh-secured-db-ledger1-run.log`. Ledger1 build exit0 / run exit1. No additional DB feature experiments in this session.

## Resumed investigation ownership and evidence

# Secured DB key-session failure

Status: OPEN P1. Owner: Codex Astra, resumed 2026-10-30.
Canonical registration: `devhub_secured_db_key_session_open_failure_2026_10_27`, TODO 377 (registration preserved in the completion branch).

The existing fresh native acceptance exited 1 at direct key-session opening,
before decoding. Prior evidence: `doc/09_report/verification/devhub_secured_db_session_close_20261027.md`.
This claim precedes source edits. Investigation owns the pure-Simple codec
boundary and `test/fixtures/devhub/fresh_secured_db/main.spl`; it does not
authorize rebuilding the compiler or restarting the exhausted RTS01 lane.

Next evidence is a diagnostic build that retains the original acceptance and
adds safe typed boundary errors. Never print secret values. Attempt 1 is
retained; this is attempt 2, capped at three distinct resumed diagnostic/fix
cycles. Unblock by isolating and fixing the actual failing boundary and passing
the exact acceptance plus an adjacent regression. Current status is unresolved.

## Resumed evidence (2026-10-30)

Attempt 2 built successfully and reproduced exit 1 with the safe typed code
`SQLCIPHER4_MISSING_SECRET`. The fresh fixture had already checked the same
environment key through `std.io_runtime.env_get`; encrypted source contents and
metadata remained unchanged. This rules out claiming the newly checked cleanup
path as the observed failure. No production source was changed.

Attempt 3 is the smaller `test/fixtures/devhub/key_resolution_probe/main.spl`.
Its native build and run exited 0: both `secret://messenger/fresh` and adjacent
dash/dot-folded reference parsing, exact environment binding, resolution of
actual ASCII bytes, and caller wipe ran. It uses the real production resolver,
not a substitute. This is a narrow control, not a full acceptance PASS.

The remaining defect is therefore dependent on the full import/call context,
or on the passphrase Result binding/key-session boundary after resolution.
Do not declare a broken environment provider globally or weaken secret checks.
Next investigation must capture safe parse/resolve/key-session boundaries in
one full-context probe and compare actual values without printing secret bytes.
The three-attempt limit is exhausted; no further retry was started. A producer
fix or newly authorized finite investigation is needed before that probe.

Evidence: `doc/09_report/verification/devhub_key_resolution_diagnostics_20261030.md`.

## Resumed evidence (2026-10-31)

Still OPEN on Phase 2. `fresh_secured_db`, built by the pinned producer
(`13d73267...`) with `src/runtime/runtime_process_tree.c` linked as an extra
object, still fails: `DIAGNOSTIC direct key session: SQLCIPHER4_MISSING_SECRET`.
The error detail printed as a raw integer (`2205408678273`); `{detail}` on a
pattern-bound enum payload is a separate defect, not yet isolated, so diagnostics
must not interpolate that payload.

Phase 1 had a different cause, now fixed: `env_get` shadowing made
`secret_ref_resolve` see a wrapped or nil value. See
`env_get_cocompiled_signature_collision_2026_10_31.md`. Moving `secret_ref` to
`env_get_opt` did not clear Phase 2; that collision was not its cause.
On Phase 1 the fixture passed direct codec and storage rows and reached
Messenger verbs; it has no final verdict yet.

## Phase 2 cause found (2026-10-31)

The Phase 2 failure was `passphrase.len().to_i64() == 0` evaluating true: see
`native_to_i64_compound_receiver_2026_10_31.md`. With the workaround the key session
opens, derived keys match hashlib, and real pages decrypt to the expected plaintext.

This bug stays OPEN because the fixture does not pass end to end. Phase 2 now opens
the database and fails reading rows: `text_from_codepoints` returns empty text, so
`SchemaNotFound` surfaces as `STORAGE_PORT_CORRUPT_SOURCE`. Messenger verbs and the
rejection checks have not run on Phase 2. On Phase 1 the fixture has no final verdict.
