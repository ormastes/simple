# Two real defects in the landed search primitives

**Date:** 2026-08-31
**Status:** OPEN — both found during integration wiring, both worked around locally
**Found by:** Q2 (duplicate-check LSH wiring + real in-process search provider)

---

## Defect 1 — `bm25_fixed_v1_score_checked` returns `invalid_parallel_arrays` for SOME caller-built inputs

**Location:** `src/lib/common/search/ranking.spl`
**Severity: medium — NOT a blanket multi-term failure. Scope corrected below.**

**CORRECTION (same day, before this record was acted on).** This was first
written up as "rejects valid multi-term queries — the main scoring entry point
is broken for the normal case". **That is false and the evidence contradicts
it:** golden vector `'alpha search'` is a genuine two-term query, and it passes
exact `score_milli` and `explanation_hash` parity end to end through
`src/lib/common/search/query_exec.spl`, which calls
`bm25_fixed_v1_score_checked` directly (line ~400). Multi-term scoring works.

What is actually true: one caller
(`src/app/spipe/search/index_engine_provider.spl`) hit `invalid_parallel_arrays`
from this function and worked around it by summing per-term contributions via
`bm25_fixed_v1_term_checked`. Since a different caller passes multi-term input
successfully, the defect is in **how that caller constructs its parallel
arrays**, or in a narrower shape the validation rejects — not in multi-term
support as such.

**Next step:** diff the `Bm25FieldV1` construction in `index_engine_provider.spl`
against `query_exec.spl`'s (which works) and find the actual difference. Do not
change the validation until that difference is identified — the validation may
well be correct and the caller wrong.

**Lesson recorded deliberately:** the original report generalised from one
failing caller to "the entry point is broken", and I propagated it without
checking. The check that settled it was cheap — look at whether any golden query
has two terms. Verify the blast radius of a defect claim before filing it at
high severity.

---

## Defect 2 — `shingles_of_tokens` aliases distinct token sequences for k > 1

**Location:** `src/lib/common/search/fingerprint.spl`

Shingles are produced by joining tokens with an **empty separator**, so distinct
token sequences collapse to the same shingle: `["ab","c"]` and `["a","bc"]` both
become `"abc"`. Under `k > 1` this makes different documents look identical to
MinHash/LSH, inflating similarity and producing false duplicate candidates.

**Workaround in place:** the duplicate-check LSH integration
(`src/compiler/90.tools/duplicate_check/lsh_prefilter.spl`) uses `k=1`, where
the aliasing cannot occur. This constrains the integration rather than fixing
the primitive — k>1 shingling is the more selective configuration and is
currently unusable.

**Fix direction:** join with a separator that cannot occur inside a token (or
length-prefix each token) so the mapping from token sequence to shingle is
injective. Add a spec asserting `["ab","c"]` and `["a","bc"]` produce different
shingles.

---

## Note on how both were found

Neither defect was visible to the package that owned the code — both required a
*consumer* to exercise the primitive for real. That is an argument for landing
integration paths alongside primitives rather than after them; a green package
suite proved less than it appeared to.
