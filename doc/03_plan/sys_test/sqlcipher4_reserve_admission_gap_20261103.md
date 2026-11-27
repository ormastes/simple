# SQLCipher4 reserve admission gap — 2026-11-03

Inspected base: be2fbbf88e12fc34a601e2da6cba01e7ae2fc7a5, current release.
Finding class: source-traced structural admission mismatch; runtime UNRUN.
Narrow production repair authored after test-first commit 2e20a20da72 and Astra source-contract review. No new bootstrap authorized.

## Specification before repair

The locked profile has 4096-byte pages and an 80-byte trailer: IV16 + HMAC64.
The storage backend decrypts 4016 body bytes and synthesizes eighty zero bytes.
The SQLite header reserve value must agree with that fixed geometry before its
view is admitted. A mismatch changes pager usable-size calculations and can
make overflow payload offsets/lengths inconsistent with the decrypted layout.

Pre-repair source trace:

1. `codec/sqlcipher4_page.spl` authenticates before CBC and checks page1 body[0:2]
   for 4096; its raw-page API does not promise full SQLite header validation.
2. `server/storage_port.spl` appends eighty zero bytes after every decoded body.
3. `_view_from_image` calls the generic SQLite header parser and copies its
   `info.reserved_bytes` into StorageReadView without SQLCipher profile checking.
4. `sqlite_format/header.spl` accepts reserve values whenever usable bytes>=480.
5. `sqlite_format/pager.spl` calculates usable_size = page_size - reserved_bytes.

Therefore authenticated reserve0/79/81 headers passed the pre-repair source gates while
the backing snapshot has an eighty-byte synthesized reserve. This is not a claim
that unauthenticated ciphertext bypasses HMAC; possession of a correct key or a
corrupted authenticated producer is required for these fixtures.

## Test-first evidence

Five independent encrypted .NET fixtures and the original 5 integration scenarios include valid reserve80,
invalid0/79/81, and invalid79 with a bad tag. The three reserve-rejection scenarios
were EXPECTED_FAIL_CURRENT_SOURCE at test-first commit 2e20a20da72 by tracing, not
observed runtime RED. The SQLCipher-specific guard is now repaired in source;
all regression execution remains UNRUN. Fixtures
and manuals carry hashes. Independently recomputed Python hashlib PBKDF2/HMAC
validated all four authentic fixture tags and rejected the one-bit bad-tag variant;
this checks fixture authentication only, not Simple execution. Two additional unit scenarios cover signed/upper page
bounds absent from the existing zero-only test. All Simple execution UNRUN.

## Authored narrow repair

In _view_from_image, after generic header parse and before view construction,
format_name == STORAGE_FORMAT_SQLCIPHER4 now requires info.reserved_bytes ==
SQLCIPHER4_PAGE_RESERVED_BYTES. A mismatch returns StoragePortError.CorruptSource;
the existing SQLCipher caller error branch wipes the reconstructed plaintext.
Generic SQLite and the raw codec are unchanged. Source-only repair is not proof
of runtime correctness; RED/GREEN execution and coverage measurement remain owed.
Do not tighten generic SQLite header handling (SQLite permits other reserves),
and do not silently tighten the partial raw page API: its existing page1 unit
fixture intentionally carries non-SQLite synthetic header data.

Authentication must still occur first. The bad-tag malformed-reserve fixture must
return authentication failure; the authenticated invalid-reserve fixtures must
return corruption. Verify valid encrypted80 plus existing plaintext SQLite tests.

Review owner: Astra; merge owner: root. No measured branch percentage and no
runtime failure/success labels are asserted by this report.

A sixth compatibility scenario (REQ-CIPHER-RESERVE-003) opens plaintext SQLite
reserve0 without a secret. Independent Python SQLite integrity_check initially
reported an 80-byte fragmentation error in this new control fixture; its producer
was corrected to set the empty leaf content offset4096, and integrity_check then
returned ok. Encrypted fixtures were unchanged. This is host fixture validation,
not Simple RED/GREEN. Mandatory runtime compiler/lib/MCP checks and docgen remain
unrun because the campaign has no admitted source-matched self-hosted runtime.
