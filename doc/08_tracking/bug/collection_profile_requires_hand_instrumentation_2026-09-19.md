# `std.common.collection_profile` is unusable without hand-instrumenting every call site

**Status:** OPEN 2026-09-19 — deliberately NOT half-built. Needs compiler
support; see "Why this is not a library change" below.
**Severity:** Medium — the profiler works exactly as specified and has zero
product callers, so the "measure before you rewrite" half of the
LLM-safe-collections feature is advice nobody can follow cheaply.
**Affected file:** `src/lib/common/collection_profile.spl`
**Spec file:** `test/01_unit/lib/common/collection_profile_spec.spl` (11/11,
all green — this is not a defect in the module's own behaviour)
**Path:** `bug` track. Found by a Fable audit of the LLM-safe-collections
("dataframe way") feature; filed instead of being partly implemented, per the
ponytail rule.

## Symptom

The module's own header states the design: "Nothing is instrumented
automatically: a caller registers named 'sites' (one per collection use worth
watching) and reports lookup/insert counts by hand." Using it therefore means
editing the code you wanted to measure:

```
var p = coll_profiler_new()
val site = coll_site(p, "user_lookup")           # register once, cold
coll_on_lookup(p, site, found, scanned_count, arr.len())   # hot path
for line in coll_advice(p):
    print(line)
```

`scanned_count` is the load-bearing argument — it is the number of elements
the lookup actually walked — and there is no way to obtain it from outside the
lookup. A caller of `arr.contains(x)` cannot report it at all without first
replacing `.contains` with a hand-written loop that counts, which is a rewrite
of the very code under measurement.

Census 2026-09-19 (`grep -rn 'coll_on_lookup\|coll_on_insert\|coll_site'`
over `src/` and `test/`, excluding the module itself): **zero** callers in
product code. Every reference is in `collection_profile_spec.spl`. The audit
had to write a throwaway script to exercise it at all.

## Measured behaviour (from the audit, for whoever picks this up)

The module itself is correct and its thresholds are pinned:

| scenario | lookups | scanned | advice |
|---|---|---|---|
| `linear_scan` | 200 | 20100 | fires — "dataframe-able ... recommend key_set/index_by" + "build once, then index" |
| `dict_index` | 200 | 200 | silent |

Threshold pins: ratio 33 at 65 lookups fires; ratio 32 at 65 lookups is
silent; ratio 100 at 64 lookups is silent. That matches
`ADVICE_SCAN_RATIO = 32` / `ADVICE_MIN_LOOKUPS = 64` with a strict `>` on
both (`scanned > lookups * 32`, `lookups > 64`).

## Why this is not a library change

Making it usable without hand-instrumentation means the compiler inserting the
`coll_on_lookup` call, with the scan count, at the sites the COLL rules
already recognise — `.contains` / `.find` / `.filter` on an array inside a
loop. That needs, at minimum:

1. **A lowering pass** that rewrites those receiver method calls into an
   instrumented form under an opt-in flag, so an uninstrumented build pays
   nothing. The COLL detector
   (`src/compiler/35.semantics/lint/collection_patterns.spl`) already
   identifies exactly these sites and now carries real spans for them
   (`is_contains_call`, `is_missing_index_call`), so site identification is
   solved; emission is not.
2. **A scan count out of the runtime.** `rt_*` array `contains`/`find` do not
   return how far they walked, and the count cannot be recovered at the call
   site. Either those primitives gain an instrumented variant or the lowering
   must expand the call into a counting loop.
3. **A profiler instance the inserted call can reach.** `coll_profiler_new()`
   returns a value the caller owns; injected code has no such value in scope.
   This needs a process-wide opt-in profiler (and a decision about what it
   does under threads — the hot path is `[i64]` slot writes with no
   synchronisation, which is fine for one owner and not fine for a shared
   global).

Points 2 and 3 are the reason this is filed rather than built: a library-only
attempt would either fabricate the scan count (making the advice unfounded,
which is exactly what the module's own header refuses to do — "Advice is
evidence, not proof") or add a global the module deliberately does not have.

## Acceptance for a fix

- An opt-in flag (e.g. `--collection-profile`) under which a program with NO
  source changes produces `coll_advice` output naming the offending site.
- The linear-scan vs Dict-index pair above, unmodified, reproduced through
  that flag: linear scan fires, Dict index stays silent.
- Zero measurable cost when the flag is off, demonstrated rather than
  asserted.
- Thread behaviour stated explicitly, not left to the reader.
