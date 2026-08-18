# Cross-Tree Stdlib Duplication Map (2026-08-18)

Audit-only. Systematic map of file-path duplication across the three parallel
stdlib trees `src/lib/nogc_sync_mut/`, `src/lib/nogc_async_mut/`,
`src/lib/gc_async_mut/`, produced as evidence for future dedup tranches
(goal 7). No source was refactored to produce this report.

## Method

1. `find` each tree, strip the tree-root prefix, sort — three relative-path
   lists.
2. Relative-path intersection (`comm -12`) pairwise across the three trees,
   unioned: **2,207** relative paths exist in 2 or more trees.
3. For each such path: `md5sum` every present copy. All-sums-equal =>
   `IDENTICAL`. Otherwise pairwise `diff`, ratio = `(changed lines) /
   max(line count)` over the worst pair. `< 10%` => `NEAR`, else
   `DIVERGENT`.

## Summary counts

| class | count | % of 2,207 |
|---|---|---|
| IDENTICAL (byte-identical, all present copies) | 434 | 19.7% |
| NEAR (<10% line-diff ratio, worst pair) | 794 | 36.0% |
| DIVERGENT (>=10% line-diff ratio) | 979 | 44.3% |
| **Total paths present in >=2 trees** | **2,207** | 100% |

Identical files by which tree-set holds them:

| tree-set | count |
|---|---|
| `nogc_sync_mut` + `nogc_async_mut` + `gc_async_mut` (all 3) | 209 |
| `nogc_sync_mut` + `nogc_async_mut` only | 220 |
| `nogc_async_mut` + `gc_async_mut` only | 4 |
| `nogc_sync_mut` + `gc_async_mut` only | 1 |

The dominant pattern is `nogc_sync_mut` <-> `nogc_async_mut` identity (429 of
434 identical files include this pair) — consistent with `http/url.spl` and
`buffer/utilities.spl` precedent.

## Top 20 largest identical files (by line count) + mergeability verdict

Verdict methodology: a file is **mergeable-candidate** if its `use`/`import`
lines (first ~6, checked directly) name no tree-specific facility (no
`nogc_async_mut`/`gc_async_mut`/GC/actor/generator-specific modules) and the
file itself does not implement a tree-differentiated wrapper. Files with zero
`use`/`import` lines are leaf/pure-logic and default mergeable pending a
closer read. This is a **candidate list**, not a merge decision — each entry
still needs the closer-read pass described in Method step 2 of the task
before any move.

| lines | path | tree-set | imports (evidence) | verdict |
|---|---|---|---|---|
| 744 | `amqp_utils.spl` | sync+async+gc (all 3) | none found | mergeable-candidate (pure logic) |
| 724 | `df/mod.spl` | sync+async | none found | mergeable-candidate |
| 699 | `allocator.spl` | all 3 | none found | mergeable-candidate — verify no raw-pointer/GC-tier divergence by full read (name suggests memory-tier sensitivity) |
| 649 | `debug/formats/test/macho_roundtrip_spec.spl` | sync+async | test fixture | mergeable-candidate (test-only) |
| 648 | `debug/formats/test/.spipe_matchers_macho_roundtrip_spec.spl` | sync+async | generated matcher file | mergeable-candidate (generated, regen not merge) |
| 637 | `src/testing/mocking_advanced.spl` | all 3 | none found | mergeable-candidate |
| 634 | `net/http.spl` | all 3 | `use std.error.*`, `use std.net.sffi.*` | mergeable-candidate — sffi import is a leaf module, not tree-specific |
| 616 | `net/telnet.spl` | all 3 | `use std.error.*`, `use std.net.tcp.*`, `use std.common.string_core.*` | mergeable-candidate |
| 616 | `debug/formats/dwarf_parser.spl` | sync+async | none found | mergeable-candidate |
| 540 | `file_system/utilities.spl` | sync+async | not checked | needs read |
| 527 | `lsp/handlers/verification.spl` | all 3 | `import lsp.protocol`, `import lsp.transport`, `use compiler.treesitter.*`, `import io.fs` | needs read — imports app-layer modules, not obviously tree-neutral |
| 516 | `debug/formats/test/golden_elf_dwarf_spec.spl` | sync+async | test fixture | mergeable-candidate (test-only) |
| 515 | `debug/formats/test/.spipe_matchers_golden_elf_dwarf_spec.spl` | sync+async | generated matcher file | mergeable-candidate (generated) |
| 500 | `diagram/__init__.spl` | sync+async | not checked | needs read |
| 491 | `lsp/handlers/completion.spl` | all 3 | not checked | needs read (sibling of verification.spl above) |
| 479 | `src/testing/mocking_async.spl` | all 3 | not checked — name implies async-tier semantics | **likely identical-by-coincidence, not by necessity** — flag for read; "async" in the name is suspicious for a file also duplicated verbatim in `nogc_sync_mut` |
| 479 | `message_transfer.spl` | all 3 | `use memory.refc_binary.*`, `use types.*` | needs read — refc_binary may be tier-specific |
| 478 | `src/testing/mock/verification.spl` | all 3 | `import testing.mock.builder.*` | mergeable-candidate |
| 473 | `engine/physics/joints.spl` | sync+async | not checked | needs read |
| 463 | `net/__init__.spl` | all 3 | `use std.net.tcp.*`, `use std.error.*`, `use std.net.udp.*` | mergeable-candidate |

## Constraint on any merge plan

**`doc/08_tracking/bug/import_triggered_cross_module_symbol_misdispatch_2026-08-18.md`**
documents that adding/moving `use`/`import` lines can trigger cross-module
symbol misdispatch. Any tranche that relocates a file to a shared owner
(e.g. under `src/lib/common/`) and re-points three `use` sites at it must
treat that re-pointing as import-graph surgery, not a pure move — verify
against that bug's repro shape before landing, and re-run the affected
trees' tests, not just the moved file's own test.

## Recommended next tranche (max 5, safest first)

Ordered by risk (lowest first): test-only fixtures and generated files first
(no runtime import-graph exposure), then pure-logic leaf files with zero
`use` lines, then files with only leaf-module (`std.*`) imports.

1. **`debug/formats/test/macho_roundtrip_spec.spl`** + its paired
   `.spipe_matchers_macho_roundtrip_spec.spl` (649+648 lines, sync+async
   identical) — test-only, no production import-graph exposure.
2. **`debug/formats/test/golden_elf_dwarf_spec.spl`** + its paired
   `.spipe_matchers_golden_elf_dwarf_spec.spl` (516+515 lines, sync+async
   identical) — same rationale.
3. **`amqp_utils.spl`** (744 lines, identical across all 3 trees, zero
   `use`/`import` lines found) — pure logic, largest single-file win.
4. **`net/telnet.spl`** (616 lines, all 3 trees, only `std.error`/`std.net.tcp`/
   `std.common.string_core` leaf imports) — precedent-consistent with
   `net/http.spl`.
5. **`src/testing/mock/verification.spl`** (478 lines, all 3 trees, only
   `testing.mock.builder` import) — mirrors the already-deduplicated
   `http/url.spl` pattern (test-support module, narrow import surface).

Explicitly deferred pending a closer read (do not include in the next
tranche): `lsp/handlers/verification.spl` / `completion.spl` (app-layer
imports, unclear tier-neutrality), `src/testing/mocking_async.spl` (name
suggests tier-specific semantics despite being byte-identical — needs
content read, not just import-line read), `message_transfer.spl` (imports
`memory.refc_binary`, plausible tier sensitivity), `allocator.spl` (name
implies memory-tier sensitivity despite zero external imports — verify
no inline tier-conditional logic before treating as mergeable).

## Raw data

Full per-file classification (2,207 rows: class, path, diff metric, tree-set)
was generated by a one-off shell script during this audit and not committed
(intermediate artifact, not a project deliverable). Re-run via the Method
above to regenerate if a future tranche needs the complete table rather than
just the top 20.
