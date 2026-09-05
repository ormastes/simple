# Duplicate Test Tree Divergence Audit (2026-08-08)

Measurement only, per request following the confirmed incident in commit
`22b8d81821` (66 missed `log_*_subsys` call sites across mirror trees,
missed twice because `grep` in this shell is `ugrep --ignore-files`, which
honours `.gitignore` and silently skips `.spipe_matchers_*`). All counts
below were produced with `/usr/bin/grep`, `find`, and `cmp`, never the
wrapped `grep`.

## 1. Enumeration of duplication

| Tree pair | Left count (`.spl`) | Right count (`.spl`) | Overlap (same relative path present in both) |
|---|---|---|---|
| `test/01_unit/` vs `test/unit/` | 11,995 | 5,103 | 5,097 (99.9% of `test/unit/` is a subset of `test/01_unit/`) |
| `test/02_integration/` vs `test/integration/` | 1,214 | 633 | 633 (100% of `test/integration/` is a subset of `test/02_integration/`) |

Only 6 files exist under `test/unit/` but not `test/01_unit/` (all GPU/hash
specs, e.g. `lib/gc_async_mut/gpu_memset_f32_fill_pattern_spec.spl`). Zero
files exist under `test/integration/` but not `test/02_integration/`. So
`test/unit/` and `test/integration/` are near-total, non-canonical
duplicates of the numbered trees, not independent content.

`.spipe_matchers_*` files: 11,954 currently on disk repo-wide. Only 4,448
sit under `test/01_unit/` and 406 under `test/02_integration/`; **zero**
sit under `test/unit/` or `test/integration/`. The remaining ~7,100 are in
`build/worktrees/`, `.claude/worktrees/`, `test/03_system/`,
`test/05_perf/`, `src/lib/`, etc. — scattered leftovers from many
concurrent/aborted runs, not a third mirror tree in the git sense.

## 2. Divergence between the two trees

Compared every path present in both trees byte-for-byte (`cmp`, not hash —
equivalent for this purpose):

| Tree pair | Common files | Byte-identical | Diverged | Divergence rate |
|---|---|---|---|---|
| `01_unit` / `unit` | 5,097 | 4,206 | **891** | 17.5% |
| `02_integration` / `integration` | 633 | 542 | **91** | 14.4% |

**Divergence is not cosmetic.** Sampled cases, by category:

- **Conflicting assertions on the same behavior** —
  `test/01_unit/os/kernel/loader/app_registry_spec.spl` expects
  `app_registry_entries().len()` to equal **19**; the `test/unit/` copy
  expects **18**, and the `test/unit/` copy is also missing a trailing
  `it` block present in `test/01_unit/`. Only one of these can be correct
  against the current implementation — the other passes by testing a
  stale contract.
- **A stub vs. a real spec, same nominal test** —
  `test/01_unit/app/dap/dap_spec.spl` runs 20 real `expect(...)`
  assertions against `src/lib/nogc_sync_mut/dap/{protocol,transport,breakpoints}.spl`.
  `test/unit/app/dap/dap_spec.spl` is a 4-line stub that just asserts a
  `pending_reason` string is non-empty, claiming DAP casts are
  "unsupported." Both are collected and run under default `bin/simple
  test`, so the suite reports two different verdicts for "DAP" depending
  on which copy a reader looks at — one real, one permanently green-noop.
- **Matcher rewrite already baked in** —
  `test/02_integration/app/loader_exec_memory_spec.spl` uses
  `assert_true(...)`; `test/integration/`'s copy uses `expect(...)` for
  the same checks — i.e. the two copies have independently absorbed a
  matcher-style migration at different times.
- **Content deletion/truncation** — several `app/dap/*_spec.spl`,
  `app/cli/*_spec.spl` files are 4–25 lines in `test/unit/` vs 25–253
  lines in `test/01_unit/` — the `test/unit/` copies were cut down to
  near-empty placeholders while `test/01_unit/` kept the full spec.
- **Semantically-inert text diff** — some pairs with identical line
  counts differ only in operator style (`opt.?` vs `opt != nil`,
  `expect(x)` vs `assert_true(x)`) with no behavior change — these are the
  harmless ~1/3 of the diverged set; the app_registry/dap cases above are
  the dangerous ~2/3.

## 3. Which tree does `bin/simple test` actually collect?

Empirically, **both**. `discover_all_requested_files` in
`src/app/test_runner_new/test_runner_main.spl:174` defaults `scan_dirs` to
`["test/"]` (whole subtree, recursive) whenever no explicit path is given,
and the only exclusion filter present (line 91) is for
`.spipe_matchers_*` / `.sspec_wrapped_entry_*` — there is no exclusion for
`test/unit/` or `test/integration/`. Confirmed against the live discovery
cache `.simple/test-manifest.idx` (19,189 entries): it holds 6,980 entries
under `test/01_unit/`, 5,055 under `test/unit/`, 740 under
`test/02_integration/`, 610 under `test/integration/` — and both copies of
`os/kernel/loader/app_registry_spec.spl` are indexed as **separate**
entries. So neither tree is dead weight in the "silently never runs" sense
— worse, in the diverged cases (§2) **both run and can report
contradictory results** for what looks like the same spec.

## 4. `.spipe_matchers_*` provenance

Generated, not hand-maintained. `src/app/test_runner_new/test_runner_single.spl:99`
builds the temp filename as
`{dir}.spipe_matchers_{pid}_{unix_micros}_{base}` and writes a rewritten
copy of the spec (infix `expect` normalization) to it as a per-run
execution target; it is meant to be transient. It's gitignored
(`.gitignore:143`) precisely because it's regenerated from the tracked
spec on every run. The 11,954 present on disk today are leftovers from
runs that didn't clean up (interrupted/killed test processes), not a
maintained mirror. Editing one by hand would be pointless — it gets
overwritten by the next run with a fresh pid/timestamp name, but a stale
leftover with an old pid could still be picked up by a subsequent grep
sweep (which is exactly what caused the confirmed incident) even though
it's never itself edited as source.

## 5. Canonical tree

`doc/07_guide/infra/test_layout_traceability.md` § "Canonical Test Roots"
explicitly lists `test/01_unit/` and `test/02_integration/` as the
canonical roots; `test/unit/` and `test/integration/` do not appear
anywhere in that doc, in `.claude/rules/structure.md`, or in
`.claude/rules/commands.md` (`bin/simple test --unit` is documented to mean
`test/01_unit/`). Git history confirms which tree is actively treated as
primary: 167 commits have touched `test/01_unit/` vs. only 12 for
`test/unit/`; 13 vs. 2 for `test/02_integration/` vs `test/integration/`.
Both trees still receive commits as recently as 2026-08-07, so this is not
a completed migration in progress — `test/unit/`/`test/integration/` are
an actively-fed shadow duplicate, not legacy debris awaiting deletion.

## Recommendation

1. **Do not blind-delete `test/unit/`/`test/integration/`.** 891 + 91 = 982
   diverged pairs need manual reconciliation first — some `test/unit/`
   copies (e.g. the matcher-style rewrites) may represent forward-looking
   edits that never made it back to canonical, and at least one
   (`app_registry_spec.spl`, 19 vs 18) needs the implementation checked to
   know which assertion is actually correct before either copy is trusted.
2. **Add a pre-push/CI guard that fails when a path present in both trees
   diverges**, comparing `test/01_unit/<p>` against `test/unit/<p>` (and
   the integration pair) by content hash. This turns silent drift into a
   loud, immediate failure instead of a sweep that "reports success" while
   missing half the call sites — the exact failure mode of the
   `22b8d81821` incident.
3. **Reconcile then delete `test/unit/` and `test/integration/`** once (2)
   is green for a period, since they are undocumented, minority-edited,
   and >99% path-subsets of the canonical trees — but only after the 982
   diverged files are triaged (keep-canonical / keep-shadow / merge,
   per-file) so no assertion is lost.
4. **Add `.spipe_matchers_*` and `.sspec_wrapped_entry_*` to the standard
   cleanup step of the test runner** (delete-on-exit or a periodic sweep)
   so the 11,954 currently-stray leftovers stop accumulating and stop
   being a source of stale, gitignored, `grep`-invisible content that a
   future sweep can miss again. Document in
   `.claude/rules/vcs.md` or a lint that any repo-wide text sweep for
   rename/rewrite work MUST use `/usr/bin/grep`, not the shell `grep`
   function, when correctness of the sweep matters — this is already
   called out in `doc/08_tracking/bug/` and in
   `MEMORY.md`'s "grep is a WRAPPED ugrep" entry, but is not enforced by
   any script.
