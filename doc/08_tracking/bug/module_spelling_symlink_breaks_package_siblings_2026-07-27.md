# Symlinked compiler tiers give the same file inconsistent module spellings, breaking directory-package sibling resolution

- **Status:** PARTIALLY FIXED 2026-07-27 (commit `3eea09c67960`) — one package
  (`compiler.frontend.core.*`) landed; the general hazard is unfixed across the
  rest of `src/compiler/`.
- **Severity:** high (stage-4 bootstrap only) — ~530 stage-4 errors traced to
  this one package; the same class is confirmed still live in at least one more
  package (`compiler.frontend.treesitter.*`, 185 `TokenKind` errors).
- **Found:** `SIMPLE_BOOTSTRAP_STAGE4=1` bootstrap lane, HIR-lowering
  unresolved-symbol sweep. Only visible under stage4: the non-stage4 bootstrap
  lane builds MIR from the flat-AST accumulator and never surfaces HIR
  lowering errors, so isolated probes and normal builds cannot detect this
  class.

## Finding

`src/compiler/` uses numbered-tier directories (`10.frontend`, `70.backend`,
`80.driver`, `60.mir_opt`, etc.) exposed to the rest of the tree via unnumbered
symlinks. Full current list (`ls -la src/compiler/`):

```
backend    -> 70.backend
blocks     -> 15.blocks
borrow     -> 55.borrow
common     -> 00.common
driver     -> 80.driver
frontend   -> 10.frontend
hir        -> 20.hir
interp     -> 95.interp
loader     -> 99.loader
mdsoc      -> 85.mdsoc
mir        -> 50.mir
mir_opt    -> 60.mir_opt
mono       -> 40.mono
semantics  -> 35.semantics
tools      -> 90.tools
traits     -> 25.traits
types      -> 30.types
```

Source discovery walks the filesystem and derives a dotted module name from
whichever path it happened to reach a given file through — the numbered path
(`compiler.10.frontend.core.lexer`), the symlinked path
(`compiler.frontend.core.lexer`), or a shortened alias
(`compiler.core.lexer`), depending on which directory entries the walker
visited first. `_driver_unique_physical_sources` then dedupes registrations by
physical file (inode/realpath), keeping only the FIRST spelling encountered —
and **which spelling wins varies per file**, not per directory or per package.

## Measured consequence

`src/compiler/10.frontend/core/lexer.spl` registered ONLY as
`compiler.frontend.core.lexer` — it was lowered ZERO times under the
`compiler.10.frontend.core.*` or `compiler.core.*` spellings. Its
same-directory sibling `lexer_scanners.spl` registered under TWO spellings:
`compiler.10.frontend.core.lexer_scanners` AND `compiler.core.lexer_scanners`.
Same directory, same discovery pass, disjoint spelling sets per file.

## Root cause

`resolve_package_sibling_symbols`
(`src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl`, ~line 881)
implements directory-package semantics: files in the same directory share a
namespace and may call each other with no `use`/import line (its own
docstring notes this mirrors the seed's flat global-registry behavior, which
gave this for free). It identifies siblings by comparing the dotted **package
prefix** of the caller's and callee's module names.

When two files in the same physical directory are registered under different
dotted prefixes (because discovery reached each of them via a different
symlink/tier path, and the dedupe step arbitrarily kept different spellings
for different files), they stop being recognized as siblings and the
no-import call convention silently stops applying.

Concretely: `lexer_scanners.spl` calls `lex_make_token` (80 call sites),
`lex_advance` (58), `lex_peek` (35), `lex_pos_get` (30) — all defined in
sibling `lexer.spl`, none imported explicitly, relying entirely on
package-sibling resolution. Once `lexer.spl` and `lexer_scanners.spl` no
longer shared a dotted prefix, every one of those call sites went unresolved,
producing ~530 stage-4 errors from this one package alone.

## Evidence

- Stage-4 unresolved-symbol count before fix: 1,681.
- After fix: 1,077 (604 fewer). The entire `lex_*` family (`lex_make_token`,
  `lex_advance`, `lex_peek`, `lex_pos_get`, …) went to zero unresolved.
- `TokenKind`-related errors (185) persisted after the fix, traced to
  `compiler.frontend.treesitter.*` — a different package under the same
  `frontend -> 10.frontend` symlink, confirming the hazard is not specific to
  the `core` package and recurs wherever discovery/dedupe picks divergent
  spellings per file.

## Fix (landed, commit `3eea09c67960`)

`_driver_module_aliases`
(`src/compiler/80.driver/driver_source_loading.spl`) previously normalized
only `compiler.10.frontend.core.*` -> `compiler.core.*`. Added the mirror
branch normalizing `compiler.frontend.core.*` -> the same canonical set, so
every file in `10.frontend/core/` registers under all three spellings
(`compiler.10.frontend.core.*`, `compiler.frontend.core.*`,
`compiler.core.*`) instead of whichever one discovery happened to keep.

## Remaining / general fix

The landed fix is **per-package** (hand-written alias branch for exactly
`frontend/core`). The underlying hazard is structural and applies to every
symlinked tier listed above, not just `frontend`. Confirmed still exposed:
`compiler.frontend.treesitter.*` (185 `TokenKind` errors, same symlink,
different subdirectory). Any other package that (a) lives under a symlinked
tier directory, (b) has cross-file no-import sibling calls, and (c) gets
inconsistent per-file spelling from discovery/dedupe is equally at risk and
currently undetected outside `SIMPLE_BOOTSTRAP_STAGE4=1`.

General fix directions (not yet implemented):
1. Canonicalize each physical file to exactly ONE module name at discovery
   time (e.g. always resolve through `realpath` and derive the dotted name
   from the numbered-tier path only), so dedupe never has a spelling choice
   to make per file, or
2. Register all valid spellings for every file uniformly (extend the
   `_driver_module_aliases` mechanism from a per-package allowlist to a
   generic symlink-aware normalizer), removing the need for hand-written
   per-package branches.

An audit of the remaining exposed packages under `src/compiler/` (`backend`,
`driver`, `mir_opt`, `blocks`, `borrow`, `hir`, `interp`, `loader`, `mdsoc`,
`mir`, `mono`, `semantics`, `tools`, `traits`, `types`, and the rest of
`frontend`) is in flight and should be linked here when it lands.

## Related

- `src/compiler/80.driver/driver_source_loading.spl` — `_driver_module_aliases`,
  `_driver_unique_physical_sources`.
- `src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl` (~line 881) —
  `resolve_package_sibling_symbols`.
- `src/compiler/10.frontend/core/lexer.spl`,
  `src/compiler/10.frontend/core/lexer_scanners.spl` — the file pair whose
  divergent spellings surfaced this bug.
- `src/compiler/10.frontend/treesitter/` — second confirmed-exposed package
  (`TokenKind`, 185 errors), fix not yet landed.
