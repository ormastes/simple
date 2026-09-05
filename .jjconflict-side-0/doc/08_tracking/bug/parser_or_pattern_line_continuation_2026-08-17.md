# Parser: a `|` or-pattern continued onto the next line does not parse

**Status:** OPEN (P2)
**Filed:** 2026-08-17
**Component:** parser (pattern parsing)
**Class:** grammar gap — a short, natural form is rejected, forcing a long-line workaround

## Symptom

A `case` alternation that wraps onto a continuation line fails to parse:

```
        case Ptr(inner, _) | Ref(inner, _) | Slice(inner) | Promise(inner) |
                ActorType(inner) | ScalableVec(inner, _):
            result = _coverage_add_type_v2(result, inner)
```

```
error: compile failed: parse: Unexpected token: expected pattern, found Indent
```

The parser accepts `|` alternations on ONE line, but a trailing `|` followed by
a newline and an indented continuation is rejected: after consuming the `|` it
expects a pattern immediately and finds the `Indent` token instead.

## Reproduction

```
bin/simple run <file containing the two-line case above>
# rc=1, "expected pattern, found Indent"
```

Collapsing the same alternation to a single line parses (`rc=0`), which isolates
the defect to the line continuation, not the patterns themselves.

## Why it matters beyond style

This is not cosmetic. It landed as a **push-blocking outage**: commit
`d9dfcbf80e0` added `src/compiler/50.mir/verification_semantic_coverage.spl`
containing the wrapped form, which made
`scripts/check/check-native-trailing-default-param.shs` exit 1 on pristine
`origin/main`, so the pre-push hook blocked **every** push for every lane. The
guard is a full-tree scan and not range-bound, so no push could avoid it.

Aggravating factor, worth fixing separately: that guard exits 1 with **zero
bytes of output** — no verdict line, no diagnosis — so the failure presented as
a broken guard rather than as a broken file. A guard that fails silently is
indistinguishable from the silent-wrong-result class it exists to catch.

## Current workaround

The alternation is kept on one line, with a comment at the site pointing here so
the next reader does not "tidy" it back into the failing form. Per the project
rule on compact forms, the workaround is recorded rather than silently
normalised.

## Fix direction

Pattern parsing should treat a `|` at end-of-line as a continuation: after
consuming `|`, skip a following newline+indent before requiring the next
pattern, mirroring how other continued expressions are handled.

## Not verified

- Whether the same limitation affects `|` alternations in other pattern
  positions (e.g. `if let`, destructuring binds) — only the `case` arm was
  measured.
- Whether a leading `|` on the continuation line (rather than trailing) parses.
