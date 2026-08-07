# Feature Expert: `resource` — origin-neutral ownership for foreign + native resources

**Docs:** research/architecture/design/plan under
`doc/{01_research,04_architecture,05_design,03_plan}/language/resource/`.
Companion feature page: `../iso_ownership/skill.md`. Assurance side:
`../mission_critical_robustness/skill.md` (REQ-MC-023 is the profile rule that
makes an unwrapped foreign handle a diagnostic).

## The idea
One nominal `resource R` declaration covers files, sockets, GPU buffers, DB
connections, locks and SFFI handles alike. Callers distinguish **ownership
semantics**, never implementation origin — there is deliberately no public
`Foreign<File>` / `Native<File>` / `SffiHandle<File>`. Plain `R` = unique affine
owner, `*R` = shared RC, `@R` = atomic RC, `-R` = weak. `close()` is a consuming
drop; methods borrow by default.

## Landed so far (2026-08-07)

| WP | Commit | What |
|---|---|---|
| WP-A | `1a6a7da02f6`, `7c60ee34bc0` | `resource` decl + `@sffi` decorator parse. **Soft keyword** — see below. Regression spec 18/18, sabotage-verified |
| WP-C | `286aa95c6f7` | All seven `@sffi` keys (`prefix`, `handle`, `invalid`, `retain`, `release`, `sharing`, `thread_safe`) round-trip into `compiler.frontend.resource_registry`, per-resource, reset per parse. 8/8, sabotage-verified |
| WP-D | `57da6077b69`, `45c0f068163` | Fail-closed convention inference (`resource_families.spl`): classifies acquire/release/retain verbs from extern names, returns an explicit error (never a guess) on ambiguity. Now 17/17 — the residual failure was `load` missing from the acquire-verb catalog (`rt_image_load` classified as method, family left acquire-less). Census coverage across the 85 families is unmeasured — Appendix A only samples, doesn't enumerate |

## Four things you will otherwise re-derive painfully

### 1. Your acceptance oracle is probably unreachable
**Do NOT write acceptance as "real source using `resource` syntax, in a spec
file."** `bin/simple test` re-execs a child **Rust seed** whose parser reads the
spec file's own module-level syntax. No pure-Simple frontend change can make that
spec parse.

Proven by **positive control**, not inference: a spec containing `layer
ProbeLayer` — an already-landed, working pure-Simple soft keyword — fails
identically with `function 'layer' not found`.

Use the **source-string harness** (the `const_spec.spl` shape): feed a source
string to `parse_module_body()` and assert on the resulting AST/registry. That is
what both passing specs above do.

By the same mechanism, **production `src/**` code cannot adopt the syntax yet** —
the seed compiles the tree. Land the pipeline behind the syntax; migrate the 85
foreign-resource families after stage-3 self-host.

### 2. `resource` MUST stay a soft keyword
There are **112** identifier uses of `resource` in `src/` (measured by
identifier-position regex; raw word count 905 includes comments and `resource_*`
compounds), **including inside the compiler's own source**. A hard/reserved
keyword breaks the compiler's own rebuild. WP-A implemented it as a soft keyword,
which makes the break structurally impossible. Related: `layer` and `cli` use
**no token constant at all** — an earlier plan note claiming "the new token is
222" was wrong, and adding one is exactly the risk being avoided.

### 3. Ownership strategy is NOT selected by the defining tier
The natural-sounding rule "`nogc_*` → affine, `gc_*` → RC" is **refuted**.
Strategy comes from **per-resource `@sffi` metadata** (`sharing:`, retain/release
presence) **plus the use-site sigil** (`R`/`*R`/`@R`) — architecture doc §3 ("RC
activates only when the program writes `*R`/`@R`") and §7 (`@R` gated on the
resource's own `thread_safe:`). Tier only constrains **legality**:
`nogc_async_mut_noalloc` forbids allocation, so wrapper-RC — which needs a
control block — is illegal there. Corroborating measurement: that tier declares
**zero** release-family externs.

### 4. Census and lexing gotchas
- **85** distinct `_free`/`_close`/`_destroy`/`_release`/`_unref`/`_dispose`
  extern families in owned code (vendor excluded, `ffi/`↔`sffi/` twins deduped).
  Per-tier declaration sites: `nogc_sync_mut` 100, `app/io` 21,
  `nogc_async_mut` 12, `gc_async_mut` 7, `common` 4,
  `nogc_async_mut_noalloc` **0**. Full table: design doc Appendix A.
- **`invalid: -1` lexes as TWO tokens.** Handling only single tokens silently
  drops the sign. WP-A folds the leading `-` into the value text; assert the
  exact string (`"-1"`), never just non-emptiness.
- **`*T` in type-annotation position already parses** — WP-B is smaller than the
  plan assumed.

## Still open
- MIR drop edges + consuming `close()` (WP-E); RC lowering (WP-B); borrow-check
  enforcement (WP-G); `sffi_gen` adapter generation (WP-H).
- REQ-MC-023 / `W-MC-RES-001` is **specified, not implemented** — no checker
  exists yet.
