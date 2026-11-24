# HIR import loading re-parses every module the loader already parsed (2026-11-24)

**Status:** FIXED (branch `work/compiler-hir-import-load-cache-20261124`)
**Area:** Rust seed — `pipeline/module_loader.rs`, `module_cache.rs`, `hir/lower/import_loader.rs`
**Found by:** exclusive profile of HIR Pass 0.5b (`load_imported_types`) on the
web renderer, tab-bar page, `SIMPLE_EXECUTION_MODE=jit`.

## Symptom

HIR Pass 0.5b took about 370 ms on tab-bar. The earlier guess was "repeat type
loads": 2,817 `load_imported_types` calls for 369 units. The exclusive profile
(nested time subtracted, label per section) showed otherwise:

| section | exclusive | calls |
|---|---|---|
| `preregister_imported_type_names` | ~245 ms | 2,612 |
| `register_imported_symbols_from_items` pass 1 + pass 2 | ~46 ms | 810 |
| import path resolution | ~29 ms | 2,817 |
| cache-hit path (defaults, traits, aliases) | ~8 ms | 1,985 |
| re-exports, trait capture, alias materialization | ~1 ms | 810 |

Memoizing the 2,612 placeholder scans per unit cut them to 326, but wall time
did not move. `preregister_imported_type_names` is simply the first code that
touches each unit. Its cost is the first `parsed_imported_module` call:
`IMPORT_AST_PARSES = 375`, `SHARED_SRC_HITS = 1`.

## Root cause

The JIT `run` path parses every imported module twice:

1. `load_module_with_imports` (the module loader) reads, strips and parses each
   file with its own `Parser`, then flattens it.
2. HIR lowering loads each module's types through the cross-lane cache
   (`parsed_imported_module` -> `shared_source_for_target`). The loader never
   filled that cache, so all 375 files were parsed a second time.

## Fix

The loader now seeds the cross-lane cache with its own parse
(`module_cache::shared_source_seed`). It does this only when the text it parsed
is byte-identical to the text the cache would parse:

- the loader parses `strip_inactive_cfg_arch_globals(strip_os_when_blocks(raw))`;
- the cache parses `strip_os_when_blocks(raw, cfg_target())`.

The same text through the same parser gives the same AST, so no lane can
observe a difference. The AST is cloned before the loader's own post-parse
`@cfg(<arch>)` fn strip. Anything else is left for the cache to parse itself:
an arch-gated global removed, bootstrap `text?` leniency, a non-host target, or
an existing or released entry.

## Evidence

- Red/green test: `compiler/tests/hir_reuses_loader_parse.rs`. Load, then
  lower; HIR must parse 0 imports (it parsed 2 before the fix, 0 after). The
  fixture includes an `@when(os=...)` module.
- tab-bar JIT counters: `IMPORT_AST_PARSES` 375 -> 5, `SHARED_SRC_SEEDS` 398.
  Max RSS is flat (2.12–2.30 GB on both binaries).
- 3-round alternating A/B, JIT wall time in ms (median), fix vs base, box load about 10:

  | page | 1x fix | 1x base | 4x fix | 4x base |
  |---|---|---|---|---|
  | animation | 3309 | 3592 | 4064 | 4368 |
  | css-layout | 3446 | 3729 | 4124 | 4463 |
  | css-paint | 3566 | 3755 | 4385 | 4658 |
  | evidence | 3228 | 3548 | 3964 | 4062 |
  | forms-media | 3428 | 3653 | 24247 | 25060 |
  | html | 3460 | 3655 | 4372 | 4506 |
  | overview | 3306 | 3522 | 3704 | 4003 |
  | tab-bar | 3237 | 3488 | 3451 | 3605 |

  Every page is faster, by 100–330 ms. The document phase (`compose_shaping`) is unchanged.
  forms-media at 4x takes about 24 s on both binaries, which predates this fix.
- Correctness:
  - 8 pages JIT==interp at 1x and 4x, and the interpreter is byte-identical to base.
  - `SIMPLE_STRICT_VREG=1` is clean on all 8 pages.
  - cargo failures equal base apart from timing flakes; all 6 differing tests pass 3/3 in isolation.
  - `batch_pipeline` and `native_link` pass. Lane gates (specs, combo matrix, Chrome catalog) pass.
- Still open: tab-bar JIT (3,237 ms) is above the interpreter (2,545 ms) at this load.
