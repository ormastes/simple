# Bug tracking rows appended outside their SDN table

Status: fix implemented; focused shell verification pending final review and merge.
Priority: P2. Bug ID: `sdn_blank_chunk_orphan_rows_2026_11_08`.
Source base: `046c85dbd887288ae5ad4e274f0b94912b13e95c`.

`SdnDatabase.load` in `src/lib/nogc_sync_mut/database/core.spl` splits its input
on literal `\n\n`. A record appended after that separator has no table header
in its section and is ignored. A correct seal authenticates those bytes but
does not put the record in a table. The shape guard previously retained the
last header across separators, hiding this loss.

The environment command in `scripts/check/bug-claim.shs` appended immediately
before the next header or EOF, after an existing separator. A focused real
writer fixture retained its original environment but lost both new records
from the header-led section, at both next-header and EOF boundaries. The
existing claim append path handled ordinary trailing separators correctly;
the repair shares one ordered append primitive between claims and environments
and inserts before the first separator. It also preserves comments between
sections, empty tables, chronological append order and existing lock/seal
publication behavior. No reader workaround or whole-database rewrite is used.

The shape guard now resets its table context at the same literal blank-line
boundary and rejects headerless data records. Fixtures distinguish a literal
empty separator from a whitespace-only line, which is not `\n\n`.

Two preexisting canonical rows for
`nativeall_stdio_facade_exports_missing_2026_11_07` occupied headerless
sections. Their exact bytes are moved into `bug_descriptions` and `bugs`.
The primary remains P1/open/valid=false: this is record preservation, not a
claim that nativeall stdio exports are qualified. All unrelated canonical
bytes and other-session dirty tracking are excluded from this change.

Both orphan insertions originated in direct database patch commit
`32904826770d75498c5b227ef0ed1d641cf0df39`. That patch does not identify the
editing tool, and the environment command does not write those tables. The
mandatory `push-sdn-row-shape` row in `config/check/must_check_gates.sdn` and
its `scripts/check/check-push-must-pass.shs` dispatch apply the strengthened
guard to outgoing database changes, including manual insertions. `bug-add`
uses the database serializer; `bug-gen` reads the database and writes
`recent_bugs.md`. The latter's line-based input and valid=false filter mean
the nativeall relocation does not add that bug to its generated open list.

The common append writer now refuses duplicate or unexpected existing table
headers rather than creating a shadow history table. New tables get a
separator even if the previous file has no final newline. Focused fixtures
also assert comment placement and preservation of rejected inputs.

The new bug record is valid=true because its existence is verified by the real
writer regression. Its repair remains pending review and merge. Only this
session's actual claim and waiting transitions are included, in chronological
order; no other session's live claims are imported.

Canonical SDN checkouts are LF by the explicit `*.sdn text eol=lf` Git
attribute. The default text reader does not normalize CR. Unexpected header
bytes fail closed instead of creating a shadow table. The tracked line-ending
policy evidence identifies the attributes and byte-preserving reader chain;
it does not claim alternate-format CRLF database support.

Focused evidence is retained in `.spipe/sdn_blank_chunk_20261108/`.
Full Simple database-loader execution is unavailable without an admitted
runtime; shell checks exercise the real writer and the owner's exact section
boundary, not a claim of compiler/bootstrap/nativeall acceptance.
