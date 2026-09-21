# Browser layout module split conservation receipt — 2026-09-21

## Scope and status

- Baseline: exact `origin/main` commit
  `e0dd873da1b7828389db4eb60e82972cc8245313`.
- Candidate branch: `fix/p1-browser-layout-module-split-20260921`.
- Bug: `browser_layout_module_exceeds_128kib_parser_limit_2026-07-31`.
- Database status: **OPEN**.  This candidate remains **HOLD** until an admitted
  pure-Simple compiler/runtime can run the parser/check and memory gates.

## Physical UTF-8 byte sizes

These are filesystem byte counts, not character counts.  The parser ceiling is
131,072 bytes.

| module | candidate bytes |
|---|---:|
| `..._core_css_rules.spl` | 52,823 |
| `..._core_selectors.spl` | 93,727 |
| `..._core_types.spl` | 7,761 |
| `..._core.spl` | 69,871 |
| `..._decl_apply.spl` | 130,751 |
| `..._declarations.spl` | 59,305 |
| `..._foundation.spl` | 118,550 |
| `..._geometry.spl` | 16,812 |
| `..._layout_engine.spl` | 125,433 |
| `..._layout_foundation.spl` | 109,272 |
| `..._layout.spl` | 95 |
| `..._paint_layout.spl` | 92,160 |
| `..._paint_primitives.spl` | 81,384 |
| `..._paint_raster.spl` | 84,577 |
| `..._paint_tiles_gpu.spl` | 14,450 |
| `..._paint_tiles.spl` | 12,889 |
| `..._style.spl` | 66,063 |
| `..._renderer.spl` | 121,014 |

All 18 family modules are below the ceiling.  The guard now discovers the
whole family, rejects missing/empty required modules, and includes
`..._decl_apply.spl`, which has only 321 bytes of headroom.

## Definition, visibility, and structural API conservation

An inventory records every top-level `fn`, `class`, `struct`, `enum`, `trait`,
`impl`, `extend`, `const`, `val`, and `var` at the exact baseline and candidate.
The exact-head review then compared every moved baseline source range with its
new owner.  All source was preserved byte-for-byte except five trailing blank
lines removed at new module boundaries; no definition body changed.  This
range comparison is the full-body conservation evidence.  An earlier helper
that stopped a definition at any unindented line did not correctly span every
multiline signature and is not relied on for the full-body claim.

| assertion | baseline | candidate | result |
|---|---:|---:|---|
| family source bytes | 1,251,448 | 1,256,937 | +5,489; no deletion |
| top-level definitions | 899 | 899 | exact |
| missing top-level definitions | 0 | 0 | exact |
| extra top-level definitions | 0 | 0 | exact |
| visibility changes | 0 | 0 | exact |
| changed moved source ranges | 0 | 0 | exact except 5 trailing blank lines |

Moved definition ownership is exhaustive:

| old owner | new owner | definitions |
|---|---|---:|
| renderer | geometry | 12 |
| core | core CSS rules | 17 |
| core | core selectors | 77 |
| core | core types | 12 |
| layout | layout engine | 8 |
| layout | layout foundation | 124 |
| paint layout | paint raster | 47 |

Lexical export-closure traversal shows the original module paths retain the
same declaration signatures and visibility:

| original facade | before | after | missing | extra |
|---|---:|---:|---:|---:|
| renderer | 845 | 845 | 0 | 0 |
| core | 468 | 468 | 0 | 0 |
| layout | 187 | 187 | 0 | 0 |
| paint layout | 276 | 276 | 0 | 0 |

The new dependency direction is acyclic within this family:

1. declarations → core types → core selectors → core CSS rules → core;
2. paint primitives → layout foundation → layout engine → layout facade;
3. layout facade → paint raster → paint layout;
4. core/paint layout → geometry → renderer facade.

No definition gained `pub`; the old facade paths remain the caller entrypoints.
This is structural API evidence.  It is not a compiler-resolved access proof:
private cross-module references such as `split_selector_groups`,
`selector_group_parts`, and `_group_specificity` still require the admitted
pure-Simple compiler/check gate.  The candidate remains HOLD for that reason.

## Red/green guard and diagnostic measurements

The identical command and identical corrected spec source were used in the
baseline and candidate worktrees:

```text
bin/simple.exe test test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_module_split_spec.spl --mode=interpreter
```

| tree | verdict | wall | peak RSS |
|---|---|---:|---:|
| exact baseline | RED, 1/3 (175,476 ≥ 131,072; 11 modules vs 18 required) | 5,005 ms | 318,238,720 B |
| candidate | PASS, 3/3 | 4,910 ms | 319,971,328 B |

Runtime identity was `D:/wk-p1-browser-layout-split/bin/simple.exe`, SHA-256
`e2a42543d62f794a8df8389de70c4200ff95675b5c48b60f0103b1f47a77e78c`,
39,066,112 bytes.  It identifies itself as a **Rust bootstrap seed**.  The
candidate was 95 ms faster in this diagnostic, while the single-sample peak
RSS was 1,732,608 bytes (0.54%) higher.  An earlier identical two-example
diagnostic recorded exactly 319,406,080 bytes for both trees.  Neither sample
is admission evidence, and the final sample does not satisfy a strict
no-increase memory gate.

These retained seed timings predate the final carrier-only hoist of
`ParsedAttr` and `ParsedSel` from core selectors into core types.  That final
adjustment moves both declaration bodies intact, changes no family byte total,
and was reviewed by source-range and dependency-direction comparison.  The
already-green seed test was not repeated solely to refresh HOLD evidence.

`simple check` was also attempted with identical target paths.  Both trees
stopped before parsing with `ERROR: no admitted cached self-hosted check worker
artifact is available`; their wall/RSS numbers therefore say nothing about
the source split.  No canonical parser/check or memory claim is made.  The DB
row stays OPEN until those gates run with an admitted pure-Simple runtime and
show no memory regression.
