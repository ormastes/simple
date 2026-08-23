# `frontend_parse_cache_scope()` latches a NEGATIVE on first call, silently disabling the parse cache for the whole process (2026-08-23)

Status: **open** — root cause located; not fixed. Reproduce cost is stated below
so whoever picks it up knows it up front.

## Defect

`frontend_parse_cache_scope()`
(`src/compiler/10.frontend/frontend_parse_cache.spl:62-70`) memoizes into
`_fe_cache_scope_memo` on its **first** call and never re-reads the
environment:

```
var _fe_cache_scope_memo: text = "@@unset@@"

pub fn frontend_parse_cache_scope() -> text:
    if _fe_cache_scope_memo != "@@unset@@":
        return _fe_cache_scope_memo
    ...
    val published = rt_env_get("SIMPLE_FRONTEND_CACHE_SCOPE") ?? ""
    _fe_cache_scope_memo = published
    published
```

`frontend_parse_cache_enabled()` is `frontend_parse_cache_scope() != ""`
(`:72`). The scope is published only by
`_driver_publish_frontend_cache_scope()`
(`src/compiler/80.driver/driver_source_pipeline_parsing.spl:198-202`), called
from `:345` and `:563` — that is, in **phase 2**.

So on any path where a parse happens in **phase 1**, the memo latches `""` and
the parse cache is **off for the entire process**, silently — no warning, no
counter, nothing distinguishes it from a cache that is on and simply missing.

That path is the **bootstrap-defaults stage build**:
`src/compiler/80.driver/driver_source_pipeline_loading.spl:60`
(`parse_full_frontend`) parses all of `src/compiler` plus
`src/lib/{nogc_sync_mut,common}` via the roots at `:126-127`, before any
publish has run.

## Why this did NOT show up in the 2026-08-23 L4 measurement

**Read this before concluding "measured fine, therefore fine."**

The L4 measurement used an `--entry` build and reported
`[frontend-cache] hits=0 misses=1 parses=1` with the cache **on**. That is not
evidence against this bug. The bootstrap-defaults roots at `:126-127` sit inside
`if input_len <= 0:` (`:118`), and an `--entry` build has `input_len > 0`, so
that whole phase-1 parse never executed and nothing called the getter early.
The latch is **latent on the `--entry`-less stage path** — which is the real
bootstrap lane, i.e. precisely the configuration nobody measured.

A green `--entry` measurement therefore says nothing about this defect. Any
future reader reaching for that measurement as reassurance is making an
`input_len` category error.

## Sibling call site — another lane's territory

`src/compiler/80.driver/driver_hir_cache.spl:70` calls the same memoized getter
and can latch it early by the same mechanism. **The HIR cache is owned by
another lane (L1/L2, `hir_cache_key` / `interface_digest_of` / `simple.sdn`
traversal); that half must be coordinated with them, not fixed unilaterally.**

## Likely minimal fix

Either:

- **Do not memoize a negative result** — treat `""` as "not published yet, ask
  again" and only latch a non-empty scope. This keeps the memo's purpose (avoid
  re-reading the env on every module) while removing its failure mode; or
- **Publish the scope before any phase-1 parse**, so the first call already sees
  the real value.

The first is smaller and does not move the publish point. Either way the cache
stays fail-closed: an unpublished scope still means "off", it just stops being
*permanently* off after a single early query.

## What a failing-pre-fix reproduce costs

A **full bootstrap-defaults stage build** (`--entry`-less), not a small closure
and not an `--entry` build — those cannot reach the defect at all, per the
`input_len` reasoning above. On a saturated box this is hours, which is why the
lane that found it was constrained not to run one. Budget for that before
starting, and assert on `[frontend-cache]` reporting a live scope (or on `.fpc`
entries appearing for `src/compiler`/`src/lib` modules) rather than on wall time.

## Provenance

Found while measuring L4 of
`doc/03_plan/compiler/bootstrap/phase1_build_duration_plan_2026-08-23.md`.
Context and the surrounding (separate) L4 finding:
`doc/08_tracking/bug/worker_children_reload_compiler_and_stdlib_uncached_2026-08-23.md`.

## Method note: a refutation must name its tree and its binary

Recorded here because it recurred across several lanes on 2026-08-23 and is not
specific to this bug.

While this was being investigated, a measurement lane reported that a claimed
cache-wipe defect was "refuted — the wide-inputs-hash path does not wipe
`frontend/`", citing `native_cache_clear_context_change` in
`bootstrap-from-scratch.sh`. That helper was the **fix**, added to that same
working tree roughly an hour earlier by the lane being reported to. The
measurement was taken against the post-fix tree and read as evidence about
pre-fix behaviour: it measured the fix and called it the bug.

**A refutation that does not name which tree (sha or worktree) and which binary
it was measured against proves nothing.** Pre-fix behaviour here was established
independently, by a guard whose selftest carries an explicit pre-fix replay
fixture and by a direct rc=1 (pre) / rc=0 (post) result — evidence that is
anchored to a stated tree state, which is what made the discrepancy visible.
