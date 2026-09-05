# Audit: non-`Result` declared return type, body returns `Ok()`/`Err()`

- **Status:** AUDITED, partial fix landed
- **Found:** 2026-08-08, follow-up to
  `try_operator_early_return_matches_neither_ok_nor_err_2026-08-07.md`
- **Claimed count going in:** 1,385 repo-wide / 888 in `src/` (unverified,
  origin unclear — not reproduced from any doc in this tree)

## Independently-derived count

Built a line-based `awk` classifier against a `git archive origin/main -- src`
extraction (14,133 `.spl` files — matches `git ls-tree -r --name-only
origin/main -- src | grep '\.spl$' | wc -l` exactly, so no symlink
double-counting from `src/compiler/{mir,driver,hir,backend}`). A hit is a
`fn`/`me` whose declared return type does not contain `Result` and whose body
contains `return Ok(...)`/`return Err(...)` or a bare `Ok(...)`/`Err(...)`
tail expression.

**Injection-tested both directions** before trusting any count:
- planted `fn parse_thing(s: text) -> text: ... return Err(...) ... Ok(s)` →
  flagged.
- planted `fn good_result_fn(...) -> Result<text, text>: ... Ok(s)` → not
  flagged.
- both checks re-run after every classifier revision below.

**The naive sweep (any `Ok(`/`Err(` in a non-Result function) found 605 hits
in `src/`.** Manually inspecting samples surfaced three legitimate patterns
the naive sweep conflates with real defects, each confirmed against actual
source and fixed in the classifier, with before/after counts:

1. **Match-arm destructuring of a Result received from elsewhere** —
   `match r: Ok(v): ... Err(e): ...`, `case Ok(v):`, and the `->` arrow form
   `Ok(v) -> v`. Example: `debug_handlers.spl:handle_debug_set_breakpoint`
   pattern-matches a `parse_int` result; it does not construct its own
   Ok/Err. **605 → 184** after excluding colon-arm and `case` forms, **184 →
   ~150** after also excluding string-embedded generator content (below),
   confirmed further down to **31** after adding the `->` arrow form and
   requiring `return Ok(/Err(` or a genuine bare-tail shape.
2. **String literals containing Rust/other-language source text** —
   `src/app/ffi_gen.specs/*.spl` and `src/compiler/90.tools/sffi_gen/specs/*`
   build FFI wrapper specs whose "body" is a *string* of generated Rust code
   containing literal `Ok(...) => ...` / `Err(...) => ...`. 35 hits, all false
   positives — excluded by directory.
3. **Docstring usage examples** — e.g.
   `src/lib/common/validation.spl:require()`'s docstring shows callers how to
   wrap its `Option` result in `Err(...)`; that's prose, not `require`'s own
   return statement. Added `"""..."""` region tracking to stop scanning
   inside docstrings.
4. **A nested `if/elif/else` value assigned to a local `val`** whose *inferred*
   type is `Result`, immediately `match`ed — the function's own declared
   return type is unrelated and correct. Example: `src/app/web_dashboard/
   tmux_api.spl:api_tmux_send` and its duplicate in `llm_dashboard/gui/
   tmux_panel.spl` always `return (i32, text, text)`; the `Err(...)` hit is
   the else-branch of a `val result = if ... else: Err(...)` sub-expression,
   not the function's own tail. Not filterable without real parsing; left as
   a documented residual false-positive risk (manually excluded from the fix
   list rather than blanket-excluded from the count).

**Final count after all four exclusions: 32 candidates in `src/`** (down from
605 naive / claimed 888). Manually verified a further false positive at this
stage too (`parse_runtime_with_mode` in `structural/parse/runtime.spl`, an
arrow-arm case that slipped past an earlier version of the arm-exclusion
regex) — **31 remaining** after that fix.

Classifier and archive kept in scratch, not committed (throwaway audit
tooling, not product code):
`/tmp/claude-1000/-home-ormastes-dev-pub-simple/895f85cb-815f-448b-86ed-4708de028caa/scratchpad/classify.awk`.

## Character of the class

**Not one refactor event — two distinct populations:**

- A **genuine defect subfamily concentrated in `src/compiler/`** (22 of the
  31 remaining hits): `predicate_parser.spl` (6), `arch_rules.spl` (1),
  `dim_constraints.spl`, `blocks/*.spl`, `type_system/effects.spl`,
  `linker_context.spl`, `vulkan_backend.spl`, `95.interp/execution/mod.spl`,
  `99.loader/module_resolver/*.spl` (3, using `T | CompileError` union types
  rather than bare non-Result — a related but distinct shape). This matches
  the "shape (d) refactor damage" story from `b0c98541d2a` /
  `9d4d16b106e2c` (impl-to-free-fn call-shape refactor): functions written
  against a `Result`-returning convention kept a stale non-Result declared
  type through the refactor.
- **Scattered, unrelated organic drift elsewhere** (2 genuine hits found and
  fixed, below, out of `src/lib` + `src/app`): one-off cases where a
  docstring already documented `Result` semantics but the signature was never
  updated to match — no shared origin, no shared commit, no shared author
  pattern found.

So: **mostly a legitimate-pattern-vs-naive-grep problem** (94% of the naive
605 were match-arm/string/docstring/nested-value false positives), with a
**real, much smaller genuine-defect core (~31 in `src/`)** that is itself two
populations — one concentrated refactor-damage family (owned, open, in
`src/compiler/`) and a handful of unrelated drift sites elsewhere.

## Family ownership check (`src/compiler/` sites)

`b0c98541d2a` and `9d4d16b106e2c` fix a *different* symptom of the same
refactor event (folded-receiver method calls / zero-definition call sites),
not this return-type shape directly — but `9d4d16b106e2c`'s own commit
message states the family is still **OPEN (29 remain)**, and
`predicate_parser.spl` / `arch_rules.spl` are explicitly named in this task's
brief as sites already claimed by that lane. Per instruction, **left
untouched** — including `expression_evaluator.spl`, which this checkout
confirms is already gone from `origin/main` `src/` (only present in stale
build/worktree snapshots), consistent with "being deleted by another lane."

## Fix landed (unowned subset)

`src/lib/nogc_sync_mut/src/dl/config_loader.spl` — two sites, no other lane
claims this file, only one internal caller for each (already pattern-matching
`Ok`/`Err`, so the signature fix changes zero call-site behavior):

- `load_config_from_file(path: text) -> DLConfig?` → `-> Result<DLConfig,
  text>`. Docstring already said "Result with DLConfig or error message";
  body is `return Err(...)` / `return Ok(loaded_config)` on every path.
- `extract_dl_config_from_sdn(sdn_value: SdnValue) -> DLConfig?` →
  `-> Result<DLConfig, text>`. Docstring already said "Ok(config) on
  success / Err(message) on invalid format".

Verified: `test/01_unit/lib/gc_async_mut/dl/config_loader_spec.spl` —
`declared>=1 executed=1 passed=1 failed=0 dropped=0`.

## Not fixed here (left for future passes)

The remaining ~29 `src/`-wide genuine hits outside the owned `src/compiler/`
family were not fixed in this pass — this was a triage/audit task, not a mass
rewrite. Re-run the classifier from scratch (fresh injection test first) to
re-derive before trusting the list again; a stale list risks fixing a file
another lane has since deleted or moved, per
`expression_evaluator.spl` above.

---

## Re-verification 2026-08-17 — named file is a FALSE POSITIVE (closed for `src/lib`)

Re-checked by CONTENT (not SHA ancestry), scoped to the file this record's
metadata names, `src/lib/common/validation.spl`.

**`validation.spl` has zero real `Ok(`/`Err(` in executable code.** The only
two hits are at lines 425 and 445, and both sit strictly INSIDE `"""..."""`
docstrings:

- `require()` — docstring spans lines **419-428**; the `return Err(message)`
  is line **425**, inside the `Usage:` example showing a CALLER how to wrap
  `require`'s `text?` return in an `Err`. `require`'s own body is lines
  429-432 (`if condition: nil else: Some(message)`) — no `Ok`/`Err` at all.
- `require_all()` — docstring spans lines **435-446**; `return Err(errors.join("; "))`
  is line **445**, again inside a `Usage:` block. Its body (447+) only pushes
  to an array and returns it.

This is exactly **exclusion category 3 ("Docstring usage examples") of this
record's own audit above, which already names `validation.spl:require()` by
name as a false positive.** The record's `file:` metadata therefore
contradicts its own body — the metadata was the triage error, not the source.
No fix is possible or warranted in this file; nothing to change.

**The "partial fix" is confirmed present in current source**, so that half of
the record is stale too:

```
src/lib/nogc_sync_mut/src/dl/config_loader.spl:22:fn load_config_from_file(path: text) -> Result<DLConfig, text>:
src/lib/nogc_sync_mut/src/dl/config_loader.spl:313:fn extract_dl_config_from_sdn(sdn_value: SdnValue) -> Result<DLConfig, text>:
```

Both signatures now declare `Result<DLConfig, text>` as the audit prescribed.

### Status

**CLOSED for the named file and for `src/lib`.** The genuine remainder is the
~29 `src/compiler/**` sites (`predicate_parser.spl`, `arch_rules.spl`,
`dim_constraints.spl`, `blocks/*.spl`, `type_system/effects.spl`,
`linker_context.spl`, `vulkan_backend.spl`, `95.interp/execution/mod.spl`,
`99.loader/module_resolver/*.spl`) already attributed above to the
`b0c98541d2a` / `9d4d16b106e2c` refactor-damage lane. Those were **not**
touched in this pass: `src/compiler/{10.frontend,20.hir,50.mir,70.backend}/**`
is out of scope for this worker, so that subfamily is **blocked-out-of-scope**,
not unproven-absent. Retitle/rescope this record to the `src/compiler/` family
rather than leaving `validation.spl` as its `file:`.
