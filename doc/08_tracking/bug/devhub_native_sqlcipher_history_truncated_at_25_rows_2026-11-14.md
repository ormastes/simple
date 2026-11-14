# Native devhub returns only the first 25 rows of a multi-page SQLCipher table

**Status:** OPEN
**Found:** 2026-11-14
**Severity:** P1 — silent data loss on read, native only (interpreter correct)

## Symptom

`devhub messenger messages --room 2` on the checked-in dense fixture
(`test/fixtures/database/sqlcipher4/dense_multipage.sqlcipher4`, 9 pages, room 2
holds 41 messages, ids 16..56) returns all 41 rows through the interpreter and
exactly 25 (ids 16..40) from a native build. Exit code 0, no warning.

```
limit=24 -> 24 rows      limit=26 -> 25      limit=41 -> 25
limit=0  -> 25           no --limit -> 25
```

There is no 25 in the messenger sources, so this is not a default limit; a limit
below 25 is honoured. Room 1 (5 rows, one of them an 11,221-byte overflow body)
reads correctly, so decryption, page auth and overflow chains are fine. The loss
starts where the table b-tree needs more than its first leaf pages.

## Repro

Seed build-commit `97728d94d5f1`, Windows, llvm-mingw 20260922.

```
SIMPLE_NATIVE_BUILD_RUST=1 SIMPLE_NATIVE_INCREMENTAL=1 simple native-build src/app/devhub/main.spl -o build/nb/devhub.exe --cache-dir build/nb/cache
DEVHUB_NATIVE_BIN=<abs>/build/nb/devhub.exe simple test test/03_system/app/devhub/messenger/messenger_read_verbs_history_edges_spec.spl
```

```
✗ returns every message of a table spread over several b-tree pages
    expected 25 to equal 41
Results: 8 total, 7 passed, 1 failed
```

Same spec without `DEVHUB_NATIVE_BIN`: `Results: 8 total, 8 passed, 0 failed`.

## Not yet known

Which layer drops the rows natively: interior-page traversal in
`sqlite_format` (b-tree / pager), or the messenger history query above it. The
library-level dense specs run interpreted only, so they do not localise it.
