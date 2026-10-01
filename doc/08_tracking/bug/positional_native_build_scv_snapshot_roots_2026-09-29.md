# Positional native-build omitted sibling modules from its SCV snapshot

## Observed failure

Linux Phase2 MCP production from frozen668 exited after 267.013 seconds.
Its positional argv had no `--source`. The admitted snapshot provenance said
`count=1`, with only `src/app/mcp/main.spl`. Four relative dependencies existed
in the source tree and were absent from the snapshot: `mcp_log_options.spl`,
`main_lazy_json.spl`, `main_lazy_protocol.spl`, and `main_static_tools.spl`.
The driver reported all four imports unresolved against the snapshot directory.

The same selection code remains in main `ba4dd5edd521f2b40584625da5671fd2faeae36d`.
`_nb_scv_freeze_v1` copied the empty supplied source-root list and appended only
the entry file. Inventory filtering correctly selected just that entry.

## Correction

The closure owner now uses one effective-root policy for its snapshot inventory,
snapshot memo key, and frozen resolver roots. Positional builds use named
`src/app`, `src/lib`, and `src/compiler` roots. An entry directory outside those
families is also included after canonical repository-relative validation.
Explicit `--source` lists retain their existing selection semantics.

Inventory admission, immutable snapshot checks, and the default refusal of an
unavailable snapshot remain required. No live source fallback was added.
This change addresses directory-contained positional entries such as MCP.
For a repository-root entry such as `main.spl`, omitted source roots are now
explicitly rejected with `SCV-E-ENTRY` and a request for finite `--source`
roots. The current selector cannot express the root's sibling files without
selecting the entire repository, which snapshot authority rejects. Explicit
source lists retain their existing entry-file inclusion and containment checks.
Root-level sibling closure remains an open limitation; this is a scoped fix for
directory-contained positional products, not a claim that every positional
entry is supported. Empty `--source`/`--source=` values are rejected by the
existing CLI option validator, rather than interpreted as omitted source roots.

## Regression and evidence limits

The focused SSpec shares its filesystem behavior with a standalone component
entry. It publishes six actual source files. The default app entry snapshot has
exactly four entry/sibling/lib/compiler files and excludes unrelated admitted
test sources. A test entry's additional parent yields all six frozen files.
An explicit app-only snapshot has exactly two files and excludes the library.
The regression also rejects explicit scope escape, excludes a real unadmitted
file, retains frozen sibling bytes
through a live edit, and requires the exact refusal for a nonexistent admitted
source in the next generation. It checks root-entry rejection and malformed
relative paths without widening explicit roots.

No full MCP, LSP, or bootstrap qualification is established by the regression.
The exhausted initial six-product batch was not retried. Component execution
and exact result are recorded separately after review.

## Separate cold refresh coordination

The LSP failure `compile-event-refresh-lock-unavailable` after 300.142 seconds
has a different cause. Concurrent children each requested cold initialization
of the common project `build/scv` journal, despite private artifact caches.
The refresh owner serializes them with a 300-second lock.

Future batch orchestration must initialize the complete src/test journal once,
then launch warm children with existing journal validation and distinct caches.
An updated pointer alone cannot authorize downgrading an explicit cold repair:
the cursor does not bind source-scope coverage. No product authority or timeout
change is made here.
