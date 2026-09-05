# Query DEPR001 Lexical Facts Specification

Source: `test/01_unit/app/cli/query_deprecated_dunder_lexical_spec.spl`
Evidence status: authored but not executed under the user-requested no-verify
override.

DEPR001 scans original source bytes and recognizes maximal ASCII identifier
tokens containing an internal `__` only when immediately followed by `(`. Names
starting or ending with `__`, digit-prefixed larger tokens, and whitespace before
the call parenthesis are excluded. Comments and ordinary/triple-string payload
are never candidates; scanning resumes after same-line or later string closure.

The executable fixture asserts five complete ordered facts from mixed source,
including two calls on one line and a real call after a triple-string close. It
pins original one-based byte columns and exclusive end columns, proves a decoy-
only source is empty, and checks exact emitted JSON for an indented call. A
bounded source contract requires byte scanning, one accepted-token slice, no
search helpers or one-byte substrings, and exactly one fact construction in the
basic lint owner.

For B source bytes, T identifier tokens, and D accepted diagnostics, the scanner
is O(B) lexical work plus emitted output, O(D) fact objects, and O(D+M) retained
scanner bytes for M total matched-name bytes. It removes the prior O(B+T) tiny
substring allocation pattern and does not construct a masked source copy. This
is one specialized lint pass;
broader future PerfFacts consolidation may combine it with other lexical rules.

## Scenario: ordered facts retain exact source spans

Given mixed comments, strings, docstrings, rejected name shapes, and valid
calls, `deprecated_dunder_facts` returns exactly these ordered facts:

``` text
Vec__new     line 2, columns 13..<21
String__from line 2, columns 26..<38
Map__get     line 6, columns 20..<28
_foo__bar    line 8, columns 1..<10
foo___bar    line 9, columns 1..<10
```

The executable assertions pin the name, line, start column, and exclusive end
column for every row, including multiple calls on one physical line and a call
after a triple-string close.

## Scenario: lexical and name-shape decoys remain silent

The executable fixture expects zero facts for comment, ordinary-string, and
triple-string payload; leading/trailing dunder names; digit-prefixed tokens; and
a name separated from `(` by whitespace.

## Scenario: both JSON owners emit the canonical span

The canonical lint collector and workspace-check collector each receive:

``` text
fn f():
    Vec__new()
```

Both executable fixtures require one `DEPR001` diagnostic at line 2, columns
5..<13 with the same message, tags, and `simple-lint` source.

## Scenario: construction remains linear and allocation-bounded

The structural contract inspects the production function and requires a byte
cursor, an accepted-name slice, no `index_of`, no `contains`, and no one-byte
substring construction. It also pins one fact-list construction in the
canonical lint emitter. Static review found O(B + output) time and O(D + M)
retained scanner memory, where M is total matched-name bytes; this claim applies
to DEPR001, not to the lint pipeline's other lexical passes.

No lint command, test, compiler, timing, allocation, or RSS execution was
performed under the user override.
