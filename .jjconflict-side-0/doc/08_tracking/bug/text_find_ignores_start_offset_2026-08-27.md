# text.find(needle, start) silently discards the start offset

- **Filed:** 2026-08-27
- **Status:** FIXED (this change)
- **Severity:** High — silent wrong answer, no crash
- **Area:** compiler string-method lowering + interpreters

## Symptom

`"abcabc".find("abc", 1)` returns `0` instead of `3`. The third argument is
accepted by every lane and then **discarded**: the call lowers to the two-arg
`rt_string_find(receiver, needle)`, which always scans from position 0.

Nothing fails. There is no arity error, no diagnostic, no crash — just a
plausible wrong answer. That is why it survived: a caller scanning forward with
an advancing position keeps rediscovering the match it already consumed.

One known victim infinite-looped a lint scan (>900s at 100% CPU; 3.4s after the
fix).

## Empirical confirmation (pre-fix, seed binary)

```
"abcabc".find("abc", 1)      => 0      WRONG (expected 3)
"abcabc".find_str("abc", 1)  => 0      WRONG (expected 3)
"abcabc".index_of("abc", 1)  => 3      correct
"abcabc".rfind("abc", 1)     => Runtime error: Function 'str.rfind' not found
"abcabc".last_index_of("abc", 1) => 3
"abcabc".contains("abc", 1)  => true   (extra arg ignored; contains has no
                                        offset form and never advertised one)
"abcabc".split("b", 1)       => [a, ca, c]   (arg is a split LIMIT, not an offset)
"abcabc".replace("a","X",1)  => XbcXbc       (3rd arg ignored; no offset form)
```

**Defective set: `find` and `find_str` only.**

`index_of` is the same underlying operation and already had a correct two-arg
form routed to the offset-aware three-arg `rt_text_find`. `find`/`find_str` are
documented aliases of `index_of` but were deliberately excluded from that route.

`rfind` fails **loudly** on a third argument — that is the correct failure mode
and is left exactly as it is. No two-arg `rfind` is added (that would be
inventing an API that does not exist). `contains` and `replace` ignore a
trailing extra argument but have never had an offset form; reported here, not
changed.

## Root cause

The offset-aware route already existed end to end — `rt_text_find(haystack,
needle, start)` is defined in **both** runtimes
(`src/runtime/runtime_native.c:3763`, `src/runtime/runtime.h:679`,
`src/compiler_rust/runtime/src/value/collections.rs:3763`) and is already
covered by runtime tests. It was simply gated on the method **name** being
exactly `index_of`. Every other alias fell through to the two-arg
`rt_string_find`, which has nowhere to put a start offset and so dropped it.

The gate was deliberate, not an oversight. `interpreter_method/string.rs`
carried this comment:

> Scoped to `index_of` only — `find`/`find_str` keep their one-arg contract
> (extra args were and remain ignored) because the compiled lane lowers only
> two-arg `index_of`, and a wider interpreter would silently diverge from it.

The reasoning was sound at the time: widening one lane alone would have created
a cross-lane divergence. The defect is that "the compiled lane doesn't support
it" was accepted as a reason to **silently ignore** the argument rather than to
either support it or reject it. This change removes the premise by widening all
lanes together.

## Fix

Widen the name gate from `index_of` to `index_of | find | find_str` at the five
sites that implement the two-arg form. **No runtime change** — neither the C
runtime nor the Rust runtime is touched, so
`check-c-runtime-compiles-push.shs` is unaffected. This is the narrowest
correct fix.

| # | Lane | File |
|---|------|------|
| 1 | Rust interpreter, string methods | `src/compiler_rust/compiler/src/interpreter_method/string.rs` |
| 2 | Rust interpreter, nested temp-text dispatch | `src/compiler_rust/compiler/src/interpreter_helpers/method_dispatch.rs` |
| 3 | Rust MIR lowering | `src/compiler_rust/compiler/src/mir/lower/lowering_expr_method.rs` |
| 4 | Pure-Simple interpreter | `src/compiler/10.frontend/core/interpreter/_EvalOps/access_literal_assign_eval.spl` |
| 5 | Pure-Simple MIR lowering | `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl` |

Comments at sites 1, 2 and 4 asserted the old one-arg contract and were updated;
leaving them would have documented the opposite of the code.

**Deliberately not changed:** the C-emitting codegen lane
(`src/compiler/10.frontend/core/compiler/cg_expr.spl`,
`cg_helpers.spl`) handles `index_of` but has **no** `find`/`find_str` arm at
all, so it never silently dropped an offset there. Adding one would be a new
feature, not this bug fix.

### Contract now pinned (identical to `rt_text_find` and to `index_of`)

Byte-indexed; raw `i64`, never an Option; `-1` for not-found; `start < 0` clamps
to 0; an empty needle answers `min(start, len)`; a non-empty needle with `start`
at or past the end answers `-1`; `start` is inclusive.

## Census of callers passing a start offset

`/usr/bin/grep -rnE '\.(find|find_str)\([^()]*,[^()]*\)' --include=*.spl src/ test/`,
vendored paths excluded per CLAUDE.md's Owned-Code Scope. 66 raw hits, of which
**26 are genuine text-`find`-with-offset call sites**; the other 40 are regex
false positives — a one-arg `.find(",")` whose comma is inside the string
literal, the unrelated filesystem `file.find(dir, pattern, recursive)`, the
user-defined HAMT `node.find(hash, key, depth)`, a user-defined
`matrix.find(target, kind)`, and `find(...)` text appearing inside string
literals in fixture content.

**24 of the 26 were actively harmful; 2 were accidentally harmless.**

Harmful — each parses or scans from a position that was silently reset to 0:

| Count | Site | Harm |
|---|---|---|
| 3 | `src/lib/nogc_async_mut/mcp/resource_utils.spl:146,155,158` | JSON array/quote scan; advancing `pos` loop |
| 3 | `src/compiler_rust/lib/std/src/mcp/core/diagnostics.spl:285,293,301` | diagnostic line/col parse, three chained `:` scans |
| 2 | `src/compiler_rust/lib/std/src/tooling/testing/parallel.spl:530,535` | pass/fail counts parsed from wrong offsets |
| 1 | `src/compiler_rust/lib/std/src/verification/lean/runner.spl:318` | `haystack.find(needle, pos)` — the advancing-position infinite-loop shape |
| 1 | `src/app/svim/_SvimCore/text_ops.spl:549` | buffer search from cursor |
| 2 | `src/app/svim/_SvimCore/session_operators.spl:152,189` | search-next always re-finds the current match |
| 4 | `src/app/test/scaffold.spl:127,240,286,291` | markdown section / code-fence extraction |
| 4 | `src/app/test/extract.spl:202,211,291,296` | markdown status / code-fence extraction |
| 3 | `test/01_unit/os/hosted/hosted_browser_renderer_entry_source_spec.spl:413,928,1037` | source-order assertions that could not actually distinguish order |
| 1 | `test/03_system/feature/app/database_resource_spec.spl:46` | JSON value scan |

Harmless — both pass a literal `0`, which the broken and fixed behaviour agree
on (the wraparound half of svim's search-next):
`src/app/svim/_SvimCore/session_operators.spl:154,191`.

No caller was found that had been written to *compensate* for the broken
behaviour, so none regresses on the fix.

## Reproduce spec

`test/01_unit/lib/std/common/text_find_start_offset_spec.spl` — covers
match-after-start, match-before-start-must-be-skipped, needle exactly at start,
`start == 0` (and equality with the one-arg form), start beyond length, negative
start, empty needle, absent needle, `find_str` alias parity, agreement with
`index_of`, and an advancing-position scan that must terminate (the
infinite-loop shape).

Verified FAILing pre-fix and passing post-fix at the assertion level (see the
verification limits below — the spec harness does not report in this worktree
for ANY spec, including pre-existing ones).

### Measured evidence

The same 13 assertions run as a direct probe against the stock seed (pre-fix)
and against a seed rebuilt from this change (post-fix):

| | pre-fix | post-fix |
|---|---|---|
| assertions failing | **10 of 13** | **0 of 13** |

Pre-fix failures included `match-after-start` (got 0, want 3),
`skip-before-start` (got 0, want -1), `empty-needle-mid` (got 0, want 2),
`find_str-alias`, `agrees-index_of`, and — the headline —
`advancing-scan-terminates`, which hit its 100-iteration safety guard instead
of the expected 3 occurrences. That last row is the infinite loop reproduced
directly: without the guard it does not terminate.

### Regression check on compensating callers

Every harmful caller was read to see whether it had been written to *compensate*
for the broken behaviour, which would make it regress on the fix. **None had.**
Both worst cases are written for the correct semantics and were simply getting
wrong answers:

- `verification/lean/runner.spl:318` `count_occurrences` is the infinite-loop
  shape verbatim (`idx = haystack.find(needle, pos)`; `pos = idx + needle.len()`).
  Pre-fix `find` kept returning the *first* occurrence, so the loop advanced only
  by its own `pos` bookkeeping and massively over-counted.
- `svim/_SvimCore/session_operators.spl:152` search-next asks for
  `find(term, start_offset + 1)` and falls back to `find(term, 0)` to wrap
  around. Pre-fix the first call always answered the match the cursor was already
  on, so "next match" never advanced.

### Honest limits of the verification performed here

**The spec harness could not be made to report in this environment, and that is
not specific to the new spec.** `bin/simple test <file>` exits 0 while printing
only lint/gc warnings and no verdict line, writes nothing to
`doc/08_tracking/test/test_result.md`, and leaves the tree clean. This was
confirmed against the **pre-existing** `text_helpers_spec.spl`, which behaves
identically — so the silence is a harness/deployment limitation of this
worktree (no full-CLI pure-Simple binary is deployed here), not evidence about
this change.

Per this repo's own guard philosophy, an exit 0 with no verdict line is not a
pass, so **no spec-level PASS is claimed**. The verification that does stand is
the 13-assertion probe above, which asserts exactly the same cases as the spec
and exercises exactly the same lowering and interpreter paths, run on the stock
seed and on a seed rebuilt from this change. The spec ships so that CI — where
the harness does report — pins the contract going forward.

### Test-side callers re-checked for regression

`test/01_unit/os/hosted/hosted_browser_renderer_entry_source_spec.spl:413,928,1037`
are the census's test-side victims and were read directly, since the harness
could not answer. All three are **ordering** assertions of the form
`expect(later).to_be_greater_than(earlier)`, built on
`haystack.find(needle, earlier_pos)`. Pre-fix the offset was dropped, so the
"later" lookup returned the *same first* occurrence as the "earlier" one and the
strict `>` could not hold on the offset-dependent rows. The fix makes these
assertions meaningful and more likely to hold — it repairs them rather than
breaking them. No test was found pinning the old ignore-the-offset behaviour
(searched for `find(..., N)).to_equal(0)` across `src/` and `test/`).

### Lane coverage note

The rebuilt-seed verification exercises the two **Rust** interpreter sites and
the Rust MIR lowering. The two pure-Simple compiler sites
(`access_literal_assign_eval.spl`, `method_calls_literals.spl`) are not
exercised by the seed binary and were fixed by inspection, mirroring the
`index_of` route already present beside them at each site.
