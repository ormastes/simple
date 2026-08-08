# Text-index CHARACTER alignment — re-scoped plan (supersedes Stage 0/1 sizing)

Third revision. The last three passes each corrected a premise of this
plan, so the plan — not the stage it was blocking — is the deliverable.
Reads only this pass; no code.

## What is now known to be wrong in the earlier docs

1. **Stage 1 census totals are BIASED, not merely lower bounds.**
   `compilability.rs` adds `FallbackReason::CollectionOps` for every
   `Expr::Slice`, marking the whole enclosing function
   interpreter-required. The census hooks sit in compile-mode HIR
   lowering, *downstream of that gate*, so they could only ever see
   functions the gate admitted — and slice-containing functions are
   disproportionately the text-parsing code being targeted. The
   headline ratio (ARRAY 1,634 : TEXT 721) and all per-primitive counts
   are quarantined. General form of the error, worth carrying:
   **a measurement placed downstream of a filter measures the filter.**
   (`Expr::Index` does NOT set a fallback reason — only `Expr::Slice`.)
2. **"Bracket hooks are dead" was never established.** That was the same
   selection effect misread as a routing fact. Retracted.
3. **"`index_of` is nearly free" conflated two populations.** 2 TEXT
   *call sites* vs ~35 *implementation files* are different things.

## `index_of` implementation census (PROVED — definitions, not call sites)

~35 files in four families, against a Stage 0 list of six (~6x undercount):

- **Runtime/engine bodies (8):** `src/runtime/runtime.c`,
  `runtime_native.c`, `runtime_legacy_core.c`, `runtime_simd_search.c`,
  `compiler_rust/runtime/src/value/{collections.rs,mod.rs}`,
  `src/runtime/simple_core/core_string.spl` (SimpleOS/baremetal),
  `src/lib/common/string_core.spl`.
- **Rust seed dispatch/codegen (9):** `interpreter_method/string.rs`,
  `interpreter_method/collections.rs`,
  `interpreter_helpers/method_dispatch.rs`,
  `codegen/instr/{calls.rs,closures_structs.rs}`,
  `codegen/llvm/{emitter.rs,functions.rs}`, `codegen/runtime_sffi.rs`,
  `hir/lower/expr/mod.rs`.
- **Self-hosted compiler tiers (9+):** `10.frontend/core/types.spl`
  (its own `str_index_of`), `cg_expr.spl`, `cg_helpers.spl`,
  `c_codegen.spl`,
  `_EvalOps/{call_method_eval.spl,access_literal_assign_eval.spl}`,
  <!-- 2026-08-01: `interpreter/eval_methods.spl` was also listed here. It was
  a DEAD duplicate (shadowed by the two `_EvalOps` files above) and was deleted
  in f97dfbbb8ee. Incidental citation only — no conclusion in this plan rested
  on it, and the two live files were already listed. See
  doc/08_tracking/bug/2026-08-01_interpreter_eval_text_method_duplicate_live_subset.md -->

  `50.mir/_MirLoweringExpr/method_calls_literals.spl`,
  `70.backend/stage4_symbol_closure.spl`,
  `80.driver/driver_source_loading.spl`.
- **Private re-implementations (~8):** `lib/common/sdn/parser.spl`
  `_sdn_index_of`; `90.tools/sffi_gen/intern_codegen.spl` `index_of` +
  `index_of_from`; `app/cli/{query_ast_query,query_sem_query}.spl`
  `_index_of_from`; `app/dashboard/dashboard_collectors.spl`
  `index_of_from`; `app/ui_edit/main.spl` `_css_index_of`.

Standing rule this produced: **census by grepping DEFINITIONS, never
call sites or dispatch tables** — the private re-implementations route
through no runtime symbol, so no dispatch-keyed census can see them.

## Closing the two INFERRED items (both now PROVED by reading)

**`runtime_simd_search.c` is genuinely byte-parallel.** `uint8_t*`
throughout; `memchr(haystack, needle[0], hlen)` for the single-byte
case; SSE2 `_mm_set1_epi8` / `_mm_cmpeq_epi8` / `_mm_movemask_epi8`
comparing 16 **bytes** per iteration; result returned as
`(int64_t)(result - haystack)` — a **byte offset**.
*Decision required before any code moves:* character offsets cannot be
produced by byte-parallel search without either (a) abandoning
vectorization, or (b) converting the byte offset to a character offset
after the match, which costs an O(match_offset) walk and reintroduces
precisely the translation cost the perf doc flags. Recommendation: keep
the SIMD search byte-native as an internal fast path and convert once at
the boundary — one conversion per *call*, not per *comparison* — and
measure it against the recorded lexer baseline.

**The private scanners RECLASSIFY — they do not hand-roll byte
arithmetic.** Bodies read:

```
fn _sdn_index_of(s: text, ch: text) -> i64:      # loops i < s.len()
    ... if s.substring(i, i + 1) == ch: return i
fn _css_index_of(haystack: text, needle: text, start: i64) -> i64:
    ... while i <= hlen - nlen: if haystack.slice(i, i + nlen) == needle: return i
```

Both are built **on the primitives** (`len`, `substring`, `slice`) and
return the same `i` they index with. They are therefore
**unit-agnostic by construction**: they inherit whatever the primitives
mean and migrate automatically *provided `len` + `substring` + `slice`
move together*. This is materially better than "8 sites embedding byte
assumptions", and it converts them from a migration cost into an
argument for the all-move-together rule.

## Named hazard: offset-parameter unit drift

**A partial migration that fixes a primitive's RETURN unit but not its
`start`/offset PARAMETER is silently wrong in the "search from here"
path.** `index_of_from(s, needle, start)` and two-arg
`index_of(s, needle, start)` (which only began existing at
`38cb691ad082`) carry the unit in *two* places. The failure is quiet:
single-argument searches keep working, so tests that don't exercise a
non-zero `start` on multi-byte input pass while the two-argument path
returns positions in a different unit than it accepts.

**Generalizes beyond `index_of`** to every primitive taking an offset —
`slice(start, end)`, `substring(start, end)`, `char_at(i)`,
`char_code_at(i)`, bracket `s[i:j]`. Rule: for each primitive, migrate
**every** index-typed parameter and the return value in one commit, and
require at least one differential test with a **non-zero offset on
multi-byte input**.

## Re-scoped workstreams

**A. Delete the private re-implementations (do this FIRST — smallest,
safest, highest leverage).** All ~8 duplicate `str_index_of` semantics
already in `src/lib/common/string_core.spl`. Deleting them in favour of
the stdlib primitive is a net-negative-lines change requiring no ABI
coordination, no engine changes, and no semantic decisions — and it
shrinks the surface every later stage must move. Do it *before* any
alignment work, so alignment has ~8 fewer places to reach. Caveat to
check per site: `_css_index_of` returns `start` for an empty needle;
confirm the stdlib primitive matches that edge before substituting.

**B. Engine primitives — all tiers per primitive, one commit each.**
Order unchanged and still justified: `index_of`/`last_index_of` →
`substring`/`slice` → bracket-slice → `len`/`length` LAST (loop bound
for every scan). Each stage begins with its own definition census (the
`index_of` count above is not transferable) and ends with the 79-site
guard population confirmed green.

**C. Census re-run (prerequisite for sizing B, not for starting A).**
Re-run with the compilability gate accounted for — either census before
the gate, or in interpreter mode — then re-derive the per-primitive
numbers. Only after this may Stage 4's bracket population be quoted.

## Sequencing consequence

**Workstream A does not depend on B or C** and can proceed immediately;
it is the only part of this campaign whose premises have survived three
revisions unchanged. Everything in B remains blocked on C for *sizing*,
though not for correctness.

## PROVED vs INFERRED

PROVED: the `compilability.rs` rule and its asymmetry between
`Expr::Index` and `Expr::Slice`; the ~35-file `index_of` census; the
SIMD byte-parallelism and byte-offset return; the two scanner bodies
quoted above.
INFERRED: that the remaining ~6 private scanners share the
built-on-primitives shape (two of eight read; signatures of the rest are
consistent); that a boundary-conversion SIMD strategy is affordable
(not measured); that `len`/`length` remains 80% of the migration-relevant
call sites (that figure comes from the quarantined census and must be
re-derived by workstream C).
