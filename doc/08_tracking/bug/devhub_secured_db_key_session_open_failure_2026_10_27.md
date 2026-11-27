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
opens, the first 4 bytes of each derived key match hashlib (full keys match in
`native_crypto_kat`), and real pages authenticate and decrypt, checked on sampled bytes.

This bug stays OPEN because the fixture does not pass end to end. Phase 2 now opens
the database and fails reading rows: `text_from_codepoints` returns empty text, so
`SchemaNotFound` surfaces as `STORAGE_PORT_CORRUPT_SOURCE`. Messenger verbs and the
rejection checks have not run on Phase 2. On Phase 1 the fixture has no final verdict.

**Revalidated 2026-11-02: still plausible because OPEN. Severity: P1. Date: 2026-10-27; no merged fix commit with a passing regression is cited in this doc.**

**2026-11-04:** root causes fixed (key session ace3ef1d00b/93a08ab43ab; text_from_codepoints da22bdea07a). text_codepoints_roundtrip_spec passes 5/5 interpreted. Verification pending: native-build test/fixtures/devhub/fresh_secured_db/main.spl on a current Phase-2 producer; close if it reaches a final verdict.

## Addendum 2026-11-11 — lane p3-caret1: key-session fix VERIFIED; row RESTORED OPEN on new downstream failure

Traversed on work/p3-caret1-20261111 (origin/release/1.0.0 tip 79d5af6723f6).

- Root-cause fix commits ace3ef1d00b1, 93a08ab43ab (key session /
  native_to_i64_compound_receiver) and da22bdea07a (text_from_codepoints) are
  all ancestors of tip.
- Native acceptance executed here, not re-read: Rust-engine native build of
  test/fixtures/devhub/fresh_secured_db/main.spl — exit 0, 198 modules,
  106.7 s (log: build/review/p3fix-caret1-20261111-logs/row5_native_build.log).
- Fixture run via provision.py --native (fresh CSPRNG secret, fresh encrypted
  inputs): the direct key session NOW OPENS (previously SQLCIPHER4_MISSING_SECRET
  at exit 1), both sample pages authenticate and decode, storage opens and reads
  46 rows — the original P1 defect is fixed.
- New failing boundary, same fixture, next stage: `FAIL fresh secured DB:
  storage first row value` — `rows[0].values[0].to_text() != "11"` (row 0 has
  7 cells, 46 rows read; the memory oracle still passes AES/KDF/HMAC/SQLite)
  (log: build/review/p3fix-caret1-20261111-logs/row5_fixture_run.log). This is a
  downstream row-cell value decode/read defect, distinct from the fixed
  key-session open; per this row's own rule ("close if it reaches a final
  verdict") it did not reach a final verdict.

Status: OPEN (restored) — original key-session failure fixed and evidenced;
remaining blocker is the downstream first-row cell value boundary above.

## Addendum 2026-11-11 — lane p3-caret2: key-session + full fixture PASS on the
## interpreter at tip; native-only row-cell failure unreproducible in this lane
## (native build blocked by known P1). Status: OPEN.

Traversed on work/p3-caret2-20261111 (origin/release/1.0.0 tip
66506fda143ca).

- The full fixture was executed here, not re-read: provision.py's canonical
  flow (fresh CSPRNG secret, fresh encrypted inputs, all variants) driving
  `bin/simple.exe test/fixtures/devhub/fresh_secured_db/main.spl
  --mode=interpreter`. Result: exit 0 — direct key session opens, both sample
  pages authenticate and decode, storage opens and reads 46 rows,
  `rows[0].values[0].to_text() == "11"` HOLDS, the overflow cell (>11000
  chars) reads, and every downstream stage passes: direct+registered storage,
  rooms/members/history/fetch/policy, wrong-secret/missing-secret/tamper
  negatives, recovery, read-only source hash (log:
  build/review/p3fix-caret2-20261111-logs/t3_fixture_run1.log). The in-tree
  row-cell decode is therefore correct; caret1's `storage first row value`
  failure is native-codegen-only.
- Native reproduction in this lane is blocked: fresh cold-cache native-build
  hangs on this host — reproduced on BOTH the full fixture closure and a
  3-import minimal repro (build logs freeze at the identical
  9919-line/925656-byte preamble with zero cache objects). This is the known
  P1 `seed_native_build_interpreted_startup_spin_2026-11-09` (BLOCKED,
  persists at HEAD, root cause in the seed-interpreted pure-Simple driver;
  needs an aarch64 cold-cache repro lane). No admitted native producer and no
  bin/release self-hosted binary exist in this environment, and a minimal
  `--source` root does not dodge the driver-startup inventory walk.
- Regression spec landed:
  `test/01_unit/lib/database/sqlite_format/devhub_rowcell_value_spec.spl` —
  2/2 PASS (interpreter). It builds the exact devhub messages shape (rowids
  11..56, unicode body, >11000-char overflow body) through
  `sqlite_format_create_image` and asserts the failing boundary and its
  neighbors through the same reader path the secured fixture exercises:
  46 rows, `rows[0].values[0].to_text() == "11"` (INTEGER PRIMARY KEY read
  as the b-tree rowid text), rowid ordering, unicode and overflow bodies.
  Sibling specs stay green (record 11/11, read_table 5/5, varint 7/7).
  Any lane with an admitted native producer can run this spec as the oracle
  for the native defect.
- Suspected native loci for the producer lane, in check order: (1) the IPK
  alias step in `sqlite_format_read_table_bytes`
  (`values[def.ipk] = DbValue.Integer(value: raw.rowid)` — `def.ipk` from the
  CREATE TABLE parse, `raw.rowid` from the leaf-cell varint); (2) the
  `DbValue.Integer` i64 match-payload interpolation in
  `src/lib/nogc_sync_mut/database/sql/types.spl` `to_text()`. A ready
  3-stage bisect repro (exact 32-byte first-row record payload + to_text
  assertions) is at
  build/review/p3fix-caret2-20261111-logs/rowcell_repro.spl with its
  interpreter oracle output in the same directory.

Status stays OPEN: the P1's native acceptance cannot be re-run to a final
verdict in this lane.
