# A NONEXISTENT method (`ByteSpan.at(0)`) silently returns 3 instead of erroring

Status: OPEN (P1)
**Found:** 2026-08-17 — interpreter, `bin/simple run` probe (no daemon involved)

## Symptom

`ByteSpan.at(0)` — a method that **does not exist** — returns `3`, exit 0, no
diagnostic. A genuinely unknown name (`no_such_method_xyz`) correctly errors.

So the failure is not "unknown methods are ignored". Some resolution path
*matches* `at` against something and yields a value, while a name matching
nothing at all is properly rejected.

`3` is the nil tag word, so the caller receives the raw tag as if it were data.

## Why this is worse than a missing method

This is a silent-wrong-result GENERATOR, not a cosmetic gap. Any caller of a
misspelled, renamed, or not-yet-implemented method gets a plausible integer
instead of an error, and the mistake propagates silently into arithmetic and
comparisons. It also means "the method exists" cannot be inferred from "the call
returned something", which undermines probe-based triage everywhere else.

## Probable neighbourhood

Consistent with the qualified-name-resolved-by-bare-last-segment family found
the same day (a qualified `EnumName.Variant` resolving by its last segment
against global tables; `me char_code_at(v)` on a struct being stolen by
`rt_string_char_code_at` through codegen qualified-name SUFFIX resolution).
A suffix/partial match on `at` is the obvious hypothesis — `at` is a suffix of
`char_code_at`, `code_at`, and others.

## Not proven
Hypothesis above is UNVERIFIED — the resolution site was not located and no
suffix-collision probe was run. Only `ByteSpan.at` was observed. Whether the
JIT/native lanes behave the same is untested.
