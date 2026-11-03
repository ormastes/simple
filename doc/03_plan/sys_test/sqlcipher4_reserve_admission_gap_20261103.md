# SQLCipher4 reserve admission gap — 2026-11-03

Inspected base: be2fbbf88e12fc34a601e2da6cba01e7ae2fc7a5, current release.
Finding class: source-traced structural admission mismatch; runtime UNRUN.
No production repair included. No new bootstrap authorized.

## Specification before repair

The locked profile has 4096-byte pages and an 80-byte trailer: IV16 + HMAC64.
The storage backend decrypts 4016 body bytes and synthesizes eighty zero bytes.
The SQLite header reserve value must agree with that fixed geometry before its
view is admitted. A mismatch changes pager usable-size calculations and can
make overflow payload offsets/lengths inconsistent with the decrypted layout.

Source trace:

1. `codec/sqlcipher4_page.spl` authenticates before CBC and checks page1 body[0:2]
   for 4096; its raw-page API does not promise full SQLite header validation.
2. `server/storage_port.spl` appends eighty zero bytes after every decoded body.
3. `_view_from_image` calls the generic SQLite header parser and copies its
   `info.reserved_bytes` into StorageReadView without SQLCipher profile checking.
4. `sqlite_format/header.spl` accepts reserve values whenever usable bytes>=480.
5. `sqlite_format/pager.spl` calculates usable_size = page_size - reserved_bytes.

Therefore authenticated reserve0/79/81 headers pass present source gates while
the backing snapshot has an eighty-byte synthesized reserve. This is not a claim
that unauthenticated ciphertext bypasses HMAC; possession of a correct key or a
corrupted authenticated producer is required for these fixtures.

## Test-first evidence

Five independent .NET fixtures and 5 integration scenarios include valid reserve80,
invalid0/79/81, and invalid79 with a bad tag. The three reserve-rejection scenarios
are EXPECTED_FAIL_CURRENT_SOURCE by tracing, not observed runtime RED. Fixtures
and manuals carry hashes. Independently recomputed Python hashlib PBKDF2/HMAC
validated all four authentic fixture tags and rejected the one-bit bad-tag variant;
this checks fixture authentication only, not Simple execution. Two additional unit scenarios cover signed/upper page
bounds absent from the existing zero-only test. All Simple execution UNRUN.

## Proposed narrow repair

In SQLCipher storage admission, after generic header parse but before constructing
the view, require info.reserved_bytes == SQLCIPHER4_PAGE_RESERVED_BYTES. Return
StoragePortError.CorruptSource, preserving the existing plaintext wipe path.
Do not tighten generic SQLite header handling (SQLite permits other reserves),
and do not silently tighten the partial raw page API: its existing page1 unit
fixture intentionally carries non-SQLite synthetic header data.

Authentication must still occur first. The bad-tag malformed-reserve fixture must
return authentication failure; the authenticated invalid-reserve fixtures must
return corruption. Verify valid encrypted80 plus existing plaintext SQLite tests.

Review owner: Astra; merge owner: root. No measured branch percentage and no
runtime failure/success labels are asserted by this report.
