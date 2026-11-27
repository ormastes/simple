# Macro namespace read coverage

Status: source under review; six parser/projector scenarios authored, UNRUN.
The goal is macro category identity and access, not a new execution engine.

The new `macro_category_complete_no_reads_v2` factory consumes the current
successful full-parse `MacroCategoryDraftV2`. It returns a completed input plus
`MacroNamespaceReadCoverageV2.NoReads` only when the exhaustive captured inventory
contains no invocation (including inactive invocations), and no definition has a
nested macro read (including unused exported definitions). The resulting input
retains all source/cfg/epoch/target/policy/executing-image bindings.

NoReads means the namespace is unobserved. It does not assert that imports expose
no macros. Therefore unrelated ordinary imports do not block this route, and the
result must never serve as a negative-name witness for another consumer. There
are no lookup records to emit. Actual file/directory source and import identities
remain necessary for whole-package reuse and future edits. Guard/effect admission
still runs through the existing category projector; this factory does not waive it.

Any invocation or nested read returns `macro-namespace-access-receipts-required`.
The future access owner may issue `ResolvedReads`; this factory never does.
Caller provenance remains required: constructible records are not authenticated
snapshots, and unsupported/opaque/failed parser capture cannot use this route.
The parent owns the actual after-source consumer and source-epoch validation.

## Audited positive-binding gap

- `core/_ParserPrimary/primary_expr.spl` records `name!(args)` and drops `!` for
  ordinary call parsing; standalone `30.types/macro_expander.spl` has fixture-only
  callers. No new executor is included in this task.
- `common/dependency/macro_import.spl` defines explicit/auto-import policy but had
  no production caller in the audited tree.
- Frozen `ModuleSurface` routes identify selected modules and aliases, but macro
  declarations are absent from its declaration/export authority. A public macro
  draft plus a target index does not prove legal access through directory facades.
- The existing `module_surface_explicit_import_origin` owner can select terminal
  origins. It must be extended with macro category/access receipts, checking every
  re-export/ancestor boundary before positive bindings become reusable authority.
- `private_fn_import_denied` is a legacy callable rule, not macro access admission;
  the diagnostic API route's `ancestor-visibility-not-collected` state is likewise
  not authority.

Full relevant import identity/access remains open until that real semantic route
exists. The no-read route provides a complete local category for ordinary projects
without inventing namespace visibility, empty definitions or placeholder hashes.
