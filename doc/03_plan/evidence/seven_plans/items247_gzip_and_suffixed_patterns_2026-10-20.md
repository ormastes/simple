# Item247 compile prerequisites: gzip and typed literal patterns

## Gzip optional filename

`gzip_header_create` now declares its existing nil-or-text API explicitly as
`filename: text?` and binds the present text before UTF-8 byte iteration. This
removes the observed erased/I64 `.bytes()` call and non-array for-in failure
without rewriting iteration or changing the emitted header format.

The five-module standalone native probe compiled with the admitted pure-Simple
producer 645e62a8, then executed with exit0 and output
`GZIP_FILENAME_NATIVE: PASS`. It checks every emitted byte for absent, present
empty, and UTF-8 λ.txt filenames. The successful compile log contains zero
const-0 placeholders. Native compiler/link subprocesses were quiescent; measured
peak RSS 3806384 KiB is diagnostic build evidence, not resource acceptance.

The first two native probe versions used direct typed-array `!=`, which reports
identity difference despite identical wire bytes. The diagnostic run printed
the exact ten expected absent-header bytes and exited10. This matches the
existing fixture-authoring issue
`doc/08_tracking/bug/type_pool_fixture_content_assertion_conversion_2026_10_16.md`;
it is not proof of a new runtime content-equality defect. The final independent
wire oracle checks length and scalar bytes. This preserves the intended header
content assertion. A later comment-only clarification in the fixture is not a
new executable test run.

Candidate SHA256: `7e67f2ee295fc8882c313acefd0e3ea01eee14c7082027c44c41c8a9c9f77bce`.
Raw compile/run logs, exact frozen-source hashes, candidate hash and supervisor
receipts are under `build/native_probe/items247-gzip-filename/`, including
`evidence.json`, `compile-wire.log`, `run-wire.log` and `process-wire.env`.
The added two SSpec cases remain unexecuted; no generated manual or full gzip
suite PASS is claimed from this standalone proof.

## Suffixed integer patterns

The db_page_decode duplicate-wildcard error has a concrete frontend cause:
EXPR_SUFFIXED_LIT was missing from pattern literal dispatch. The source repair
preserves literal casts and normalizes integer-only casts to typed HIR integer
predicates before MIR dispatch. Five regression scenarios cover the actual
byte-tag pattern family and width/cast controls. See
`doc/08_tracking/bug/suffixed_match_literals_become_wildcards_2026_10_20.md`.
This compiler repair remains UNVERIFIED until a producer containing it is built.

## Current landing boundary

Full Phase3 remains unqualified. Struct equality prerequisites and the retained
item2/4/7 requirements remain open. Concurrent boot6 Stage3 and boot7 Stage2
processes were found live during this turn; neither was modified and no duplicate
full bootstrap was launched. Available disk space declined to 31 GiB, while this
lane's native-probe files totaled 20 MiB and its SCV snapshots about 1019 MiB; no
attribution of other disk usage or cleanup of other owners was performed.

A further current-source check shows item4's packed-byte ELF-input change is
already present in release_phase3: e69519b2d9c keeps ElfLinkRequest objects and
archives as [[u8]]. The old widened-input bug document has not caught up with
that implementation. Its full-scale qualification must still be checked, but
the implementation must not be recreated from the stale bug description.
