# Seed: `text.len()` counts chars but `text.slice()` cuts bytes; non-ASCII makes a pure-SQL file DB unreopenable

Status: verification-pending
Date: 2026-11-16
Area: seed interpreter text ops / `src/lib/nogc_sync_mut/database/pure_sql/_PureDatabase/row_value_helpers.spl`

## Symptom
On a Korean-locale Windows host, `bridge_worker --once` against a closed port
stores the OS error text (`... 대상 컴퓨터에서 연결을 거부했으므로 ... (os error 10061)`)
in `outbox.last_error`. Reopening the same DB file then fails:
`Connection failed to '<db>': noncanonical pure database v3 record escape`.
`PureSqlMessagingStore.open` unwraps that error and the process dies with
`error: called unwrap on Err`. So any non-ASCII text (localized OS errors, chat
bodies in Korean) makes a file-backed messaging store unreopenable under the seed.
This is data-loss class.

## Repro (seed-vtable.exe `run`)
```
fn main():
    val s = "a대b"
    print "len=" + s.len().to_text()
    var i = 0
    var out = ""
    while i < s.len():
        out = out + s.slice(i, i + 1)
        i = i + 1
    print "rebuilt_eq=" + (out == s).to_text() + " out=" + out
main()
```
Output: `len=3`, `rebuilt_eq=false out=a�`. `len()` is in chars and `slice()` is in bytes.

## Why the DB breaks
`_pdb_v2_unescape` walks the record char by char with `slice(i, i + 1)` up to
`len()`, and `_serialize_row_v2` / `_deserialize_row_v2` frame text cells with
`payload.len()` and read them back with `slice`. With mixed units the unescaped
record does not re-escape to the same bytes, so the v3 canonicality check fails.

## Needed
Make seed `slice` and `len` use the same unit as pure Simple. The owner rule is
that seed text indexing must match pure Simple. Patching the DB codec alone
would move the failure into the length framing. Native behaviour is not yet
measured.

Found by the bridge_worker HTTP delivery lane (`work/bridge-worker-http-shared-20261116`).
The shipped spec there drains an in-memory store, so it does not depend on this bug.

## Resolution (2026-11-16, `work/pure-db-multibyte-escape-20261116`)
The seed is not wrong. The owner decision of 2026-11-07
(`doc/07_guide/quick_reference/syntax_quick_reference.md`, "Length and slicing
units") makes `len()` count code points and `slice`/`substring`/`byte_at` take
byte offsets. The bug was in the pure-DB codec, which bounded byte scans by
`len()`. Fix: every scan and length frame in the v3 codec now uses
`byte_len()` (`_pdb_v2_unescape`, `_serialize_row_v2`, `_deserialize_row_v2`,
`_pdb_v3_row_encoding_is_canonical`, `_pdb_decimal_parse_strict`, and the
envelope length in `pure_database.spl`). `_pdb_v2_unescape` copies whole runs
between `%` escapes, so a multi-byte character is never cut. Files written
before the fix that hold non-ASCII text could not be reopened anyway. ASCII
files are byte-identical.

Spec: `test/01_unit/lib/database/pure_sql_reopen_multibyte_text_spec.spl`
(Korean, `é`, emoji round trip; a damaged non-ASCII file returns `Err`).
Not yet checked: native build. `PureSqlMessagingStore.open` still unwraps the
open result. That is a separate safe-code panic and was not changed here.
