# `_`-Prefixed Folders — Transparent Packages

**Status:** resolver fallback implemented in the pure-Simple module resolver;
first migration (`_SocVhdlGen/`) landed and verified on the seed. Full
transparency (importers unchanged after a move) goes live on the self-hosted
binary post-bootstrap — see *Two resolvers* below.

## Why

Big classes get split across several files. The old convention left numbered
sibling files (`foo_part1.spl`, `foo_2.spl`) or a re-export shim. That clutters
the parent folder and bakes the split into every importer's `use` path.

A `_`-prefixed folder lets a class own a folder for its pieces while the folder
stays *transparent* to module resolution.

## Semantics

A directory whose name starts with `_` is a **transparent package**: its files
resolve as if they sat directly in the nearest non-`_` ancestor folder.

- Move `bcrypt/hash.spl` into `bcrypt/_BcryptHasher/hash.spl` and
  `use std.bcrypt.hash` keeps resolving — the `_BcryptHasher/` segment
  contributes nothing to the module path.
- **Siblings still see it.** A sibling file or sibling folder imports the class
  exactly as before. No new `use`, no path change.
- **Recursive.** `_A/_B/x.spl` resolves as `<parent>.x`; grandchildren under
  nested `_` folders bubble up to the first non-`_` ancestor.
- **Files unaffected.** Only *directories* whose name starts with `_` are
  transparent. `_*.spl` files (`__init__.spl`) and trailing-underscore names
  (`impl_/`) keep their current meaning.

Same idea as the existing numbered-directory rule (`NN.name` strips the `NN.`
prefix), one step further: a `_` directory strips its *whole* segment.

## Resolution algorithm

Implemented in
`src/compiler/10.frontend/core/interpreter/module_loader_resolve.spl` as an
**additive final fallback** in `_resolve_module_path_uncached` — runs only after
every existing strategy (local, `SIMPLE_LIB`, `src/`, lib-family, numbered-dir)
misses, so successful imports pay zero extra cost and existing resolution is
unchanged. Helpers: `_find_transparent_file` (recursive `_`-descendant search),
`_walk_dir_chain`, `_resolve_transparent`; bases = importer dir, `src/`, and the
`src/lib/<family>/` GC search order. Standalone-validated 4/4 (direct, recursive
grandchild, miss, empty-parts).

## Two resolvers (deploy reality)

The running `bin/simple` is the prebuilt **Rust seed**; it resolves modules with
its own native resolver
(`src/compiler_rust/compiler/src/hir/lower/import_loader.rs`), **not** the
pure-Simple resolver edited here. The fix lives in the pure-Simple resolver
because that is the correct owner per the repo's pure-Simple directive (the seed
is bootstrap-only). Full transparency (drop the `_X` segment from importers) goes
live on the **self-hosted** binary after a bootstrap rebuild + deploy *if* that
binary's `run`/`test` path routes resolution through this interpreter resolver —
unconfirmed vs. `src/compiler/35.semantics/resolve.spl` and
`src/compiler/99.loader/loader/module_loader.spl`; check before relying on the
segment-drop form. Rebuild/deploy is human-gated and bootstrap stage-3 is
currently broken. Porting the rule to the Rust seed is deliberately out of scope.

## Migration

`_ClassName/` is a stepping stone, not a terminal state:

1. **Now:** split a big class into `_ClassName/` with semantically-named files
   (`token_scanner.spl`, not `part1.spl`).
2. **Later:** promote to a real `_package/` (still transparent) or a plain
   `package/` (addressable — importers add the explicit `use`).

**Doing it safely today (before full transparency is live):** move the files
into `_ClassName/` *and update the aggregator/importers to the new
`…._ClassName.<name>` path*. The seed treats `_ClassName` as an ordinary path
segment, so this resolves immediately — external code that imports through the
aggregator is untouched. Once the self-hosted transparency is live, the `_X`
segment can be dropped from the importers.

### Worked example — `_SocVhdlGen/` (landed)

`src/lib/hardware/fpga_linux/`:

- `soc_vhdl_gen_part1.spl` → `_SocVhdlGen/peripherals.spl`
  (BRAM/ROM/RAM, UART, CLINT, mailbox, interconnect generators).
- `soc_vhdl_gen_part2.spl` → `_SocVhdlGen/top_testbench.spl`
  (top-level SoC assembly + simulation testbench).

Split by **semantic role** (peripheral generators vs. top assembly+testbench),
not by line count. Aggregator `soc_vhdl_gen.spl` updated to
`export use lib.hardware.fpga_linux._SocVhdlGen.{peripherals,top_testbench}.*`;
`__init__.spl`'s stale `export soc_vhdl_gen_part2` removed (its symbols now flow
through `export soc_vhdl_gen`). Verified on the seed: `generate_uart_vhdl()`
(peripherals) and `generate_soc_top_vhdl()` (top_testbench) both resolve and
return content. Model that chose the division: Opus 4.8.

The other 180 numbered class-splits (mostly bootstrap-critical `src/compiler/**`)
are **not** swept blind — each must be migrated and verified individually using
the aggregator-update pattern above, and the compiler ones only with a green
bootstrap.

## Conflicts removed

Owned source (`src/**`, excluding vendored trees) had **zero** `_`-prefixed
directories before this work, so the rule removed no existing owned behaviour.
The trailing-underscore `impl_/` is not matched by the leading-`_` rule.

## Warnings

After moving files into a `_ClassName/` folder, fix any `unused`/`private`/
import lint the move surfaces — the symbols stay public to siblings, so a
warning treating a `_`-folder member as unreachable is a false positive to
silence at the lint, not by re-exporting.
