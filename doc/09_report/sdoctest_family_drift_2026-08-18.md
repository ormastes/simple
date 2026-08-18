# sdoctest four-family drift — investigated, NOT drifted (2026-08-18)

Lane: DRIFT. Verdict: **NO semantic divergence. Zero doctests can be missed by
family choice.** The premise ("four copies of the extractor") is false as of
this tree: there is exactly ONE implementation and three re-export facades.

## 1. What is actually there

`wc -c` over `src/lib/<family>/test_runner/sdoctest/*.spl`:

| family | total bytes | nature |
|---|---|---|
| `nogc_sync_mut` | 64,029 | **the only implementation** |
| `nogc_async_mut` | 4,348 | facade -> `nogc_sync_mut` |
| `gc_async_mut` | 4,377 | facade -> `nogc_async_mut` |
| `gc_sync_mut` | 2,600 | facade -> `gc_async_mut` |

Delegation chain (verified on every one of the 10 files):

```
gc_sync_mut -> gc_async_mut -> nogc_async_mut -> nogc_sync_mut  (impl)
```

Evidence, `extractor.spl`, all three facades are their whole file content:

- `src/lib/gc_sync_mut/test_runner/sdoctest/extractor.spl:3`
  `export use std.gc_async_mut.test_runner.sdoctest.extractor.*`
- `src/lib/gc_async_mut/test_runner/sdoctest/extractor.spl:1-3`
  `export use nogc_async_mut.test_runner.sdoctest.extractor.{extract_sdoctest_blocks, extract_blocks_from_content}` (+2 more lines)
- `src/lib/nogc_async_mut/test_runner/sdoctest/extractor.spl:1-3`
  `export use nogc_sync_mut.test_runner.sdoctest.extractor.{...}`

Same shape for `test_manifest.spl` (12,408 B impl in `nogc_sync_mut`; 320/278/58 B
facades), `test_manifest_scanner.spl` (10,376 B impl; 317/278/66 B facades) and
`doctest_runner.spl` (17,033 B impl; 257/58/59 B facades).

## 2. Semantic differences — NONE

The recognition predicate, supported comment markers, fence handling
(`parse_fence_line`, `parse_modifiers`), root configuration
(`load_sdoctest_config`, `find_env_run_config`) and ignore/skip logic
(`is_ignored`, `is_tag_ignored`, `SdoctestModifier`) exist in exactly one place,
`src/lib/nogc_sync_mut/test_runner/sdoctest/`. Facades contain no logic at all —
only `export use` lines. There is nothing to diverge.

## 3. How a run reaches a copy — by import path, deterministically

`use std.test_runner.sdoctest.X` does NOT resolve to a `src/lib/test_runner`
directory (it does not exist). It falls through to the family search in
`src/compiler/10.frontend/core/interpreter/module_loader_resolve.spl:220-250`,
whose order is fixed and documented at `:216-219`:

```
nogc_async_mut > nogc_async_immut > nogc_sync_immut > nogc_sync_mut
> common > gc_async_mut > gc_async_immut > gc_sync_mut > gc_sync_immut
> nogc_async_mut_noalloc
```

So a bare `std.test_runner.sdoctest.*` import binds to the **`nogc_async_mut`
facade** (first existing hit), which forwards to `nogc_sync_mut`. Not
accidental — it is the first-match rule, and every arm of it terminates at the
same implementation. All six non-test importers use the bare `std.test_runner`
form; the only family-explicit importers are the two facade contract specs
(`test/01_unit/lib/{gc_async_mut,nogc_async_mut}/test_runner/sdoctest/sdoctest_facade_spec.spl`).

## 4. Blast radius

**COUNT: 0 doctests.** Not an estimate — a single extractor implementation
cannot recognise different example sets for different callers. No upper bound is
needed because the population of divergent logic is empty.

## 5. Residual finding (cosmetic, not a defect): narrowed facade surface

The two middle facades re-export *named* symbol lists, not `.*` (only
`gc_sync_mut` uses `.*`). Comparing declared symbols in the impl against the
names listed in the `nogc_async_mut` facade:

| module | impl syms | re-exported | not re-exported |
|---|---|---|---|
| `config` | 12 | 7 | `line_indent`, `make_source`, `parse_inline_array`, `parse_kv`, `strip_quotes` |
| `discovery` | 6 | 4 | `extract_basename`, `list_contains` |
| `doc_gen` | 2 | 1 | `truncate_text` |
| `glob` | 4 | 2 | `glob_match_chars`, `glob_match_parts` |
| `extractor` | 7 | 5 | `line_indent_count`, `strip_doctest_prompts` |
| `runner` | 12 | 7 | `find_sdoctest_binary`, `format_modifiers`, `platform_binary_candidates`, `print_file_result`, `print_sdoctest_list` |
| `types` | 21 | 11 | 10 `has_modifier_*` / `get_*` / `is_ok` accessors |
| `result_db` | 2 | 2 | — |

Every withheld name is an internal helper. Checked for external callers
(`src/app`, `src/compiler`, `test`, excluding `src/lib`): `line_indent_count`,
`has_modifier_ignore`, `print_sdoctest_list`, `is_tag_ignored` have **zero**;
`strip_doctest_prompts` and `find_sdoctest_binary` appear only inside comments;
`has_modifier_skip` is called as a **method** on a block value
(`test/01_unit/lib/test_runner/sdoctest_extractor_spec.spl:32`), which travels
with the re-exported `SdoctestBlock` type and is therefore unaffected by the
free-function list. **No caller is blocked.** Not filed as a bug.

## 6. Recommendation: keep it, do nothing

Consolidation is already DONE — this facade chain *is* the output of the active
de-duplication effort (`refactor(dedup)` / goal 7 commits: `9fbd3cd8ddc`,
`a6b0ced06f2`, `3c8a8b716d1`, `d0c0da23b91`; map at `0257cdd71f4`). The four
directories must remain because the family search in `module_loader_resolve.spl`
is path-based: deleting `src/lib/nogc_async_mut/test_runner/sdoctest/` would make
`use std.test_runner.sdoctest.*` resolve to `nogc_sync_mut` instead — the same
code, but it would silently change GC-family boundary classification
(`src/compiler/35.semantics/gc_boundary_check.spl:164`) for every importer. The
facades are load-bearing, cost ~11 KB total, and carry no logic to drift.

Optional, low value: widen the two named-list facades to `.*` for surface parity
with `gc_sync_mut`. Not required, not proposed here.

## Method / non-vacuity (per `doc/07_guide/infra/detector/detector_standard.md`)

Items examined, all > 0: 40 sdoctest files (10 x 4 families) + 12
manifest/doctest_runner files; 8 modules symbol-diffed; 8 withheld symbols
grepped for external callers; 1 resolution rule read at source. No command's
exit code was read through a pipe. Nothing was rebuilt or redeployed.
