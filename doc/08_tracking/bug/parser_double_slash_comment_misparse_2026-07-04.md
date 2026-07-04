# Parser: `//` comments are silently misparsed as code

**Date:** 2026-07-04
**Severity:** medium (silent; errors surface on the NEXT statement)
**Status:** open — workaround: only `#` comments

## Symptom

Simple's comment syntax is `#`. A `//` line is not rejected as a syntax
error; instead its bare words are parsed as expressions/identifiers, and the
failure surfaces as a misleading `semantic: variable X not found` on the
FOLLOWING statement (X being a word from the comment).

## Repro

```
// this explains the next line
val y = 2
```
→ `semantic: variable this not found` (or similar), attributed near `val y`.

Found 2026-07-04 in a test spec authored by an agent lane; both occurrences
fixed by switching to `#`. Agents (and humans coming from C-family
languages) will keep writing `//` — the silent misparse costs real
debugging time.

## Fix direction

Lex `//` at statement start (or after whitespace) as a hard error with a
"use # for comments" hint — or accept it as a comment. Silence is the only
wrong option.
