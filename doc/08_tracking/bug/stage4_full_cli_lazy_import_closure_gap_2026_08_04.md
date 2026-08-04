# Stage 4 full CLI lazy-import closure gap

## Status

Claimed after the first post-AST-slot Phase 4 cycle on 2026-08-04.

## Reproduction

The refreshed pure-Simple Stage 3 compiler released all 1,726 streaming
surfaces and completed HIR lowering, then rejected ten calls in
`app.cli._CliMain.main_and_help` as unresolved.  Eight names are declared by
four explicit `use lazy` command-tool imports; two frontend-delegation helpers
were also absent from the explicit `app.io.cli_ops` item list.

The ordinary source-dependency scanner intentionally excludes lazy imports,
which is correct for interpreted startup.  The exact Stage 4 one-binary CLI,
however, statically lowers every command branch and therefore needs those
declared owners in its entry closure.  Skipping them removes both their module
surfaces and link definitions before HIR can register the named imports.

## Repair boundary

Preserve the ordinary scanner's lazy exclusion.  Add an explicit Stage 4
scanner mode that includes real `use lazy` declarations while retaining the
same cfg, comment, and docstring filtering, and select it only in the exact
Stage 4 entry-closure walks.  Import the two existing `cli_ops` helpers
explicitly.  Do not make all ordinary closures eager and do not permit
unresolved/stub symbols.

## Required evidence

- Unit coverage proves ordinary closure scanning still skips lazy imports and
  Stage 4 scanning includes them.
- The next bounded exact Phase 4 cycle crosses all ten unresolved names.
- The exact candidate must still pass the essential test, lint, and duplicate
  command smoke; mere HIR success is not completion.
