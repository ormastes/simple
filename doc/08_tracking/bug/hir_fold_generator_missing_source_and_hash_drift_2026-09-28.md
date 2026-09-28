# HIR fold generator: missing source and separate digest drift

Status: import blocker fixed in isolation; full bootstrap and generator
freshness are not certified by this change.

## Windows Stage2 failure

Pinned main `aa61760f346815f394910266d3f91345a0efef8a` compiled 1,061 files,
reused zero, and failed only `src/compiler/20.hir/generated/hir_visitor.spl`.
Line 14 imported `common.facet_abi.*`; the compiler reported E1034 because
`common` could not be resolved. No Stage2 candidate or receipt was produced.
The same bad configuration remains on fix base
`b472cd23ff6249d6ae283225fb38b9cb31ec58b8`.

`fold_gen.spl` configured nonexistent `src/lib/common/facet_abi.spl` and its
import. `DeclUniverse.load_from` silently skipped the missing source while
the generator retained the import. Regeneration commit `cd40f7e763d` exposed
this stale configuration in checked-in output. Existing HIR definitions and
types contain every required declaration; no facet symbol needs replacement.
This is a generator configuration issue, not Windows alias materialization.

The fix removes both stale entries, rejects any missing configured dialect
source before loading, and adds a partial-missing-source case to the existing
freshness selftest. The HIR visitor body was regenerated with the canonical
generator. Its unchanged schema hash header is preserved for the separate
digest issue below; no generated AST changes are included.

## Focused evidence

Isolated checkout: `D:/dev/simple-hir-visitor-fix-20260928`.
Bootstrap authority: frozen seed from the failed run, SHA-256
`3b6d96f6fb18c7aea690f26b61b36d5a2757db37e1a799fbd4cca442d35d575a`.
The installed Windows release-path executable also identifies itself as a
Rust seed. These are bootstrap repair probes, not self-hosted test evidence.

- Canonical `run src/app/compiler_schema/main.spl folds` emitted two visitors.
- Focused LLVM native build: 43 compiled, zero failed, no unresolved stubs;
  3.9s compile + 3.7s link, 7.5s reported total. SCV fallback was unset.
- Partial-source fixture retained `hir_definitions.spl` but omitted
  `hir_types.spl`; generation returned 1 and named
  `E-FOLD-SOURCE-MISSING: src/compiler/20.hir/hir_types.spl`.
- An initial unit-runner attempt failed before assertions with unrelated
  `unknown extern function: rt_env_vars`; no unit-test PASS is claimed.

Commands, fixtures and logs are retained in
`build/mini_builds/hir-visitor-fix/`: `compile-visitor.ps1`, `native-build.log`,
`partial-source.log`, `generate-folds-canonical.log`, and the hash probes.
The frozen full-run evidence remains in
`D:/dev/simple-windows-stage234-20260928/build/mini_builds/windows-stage234/RESULT.md`.

## Separate digest defect and freshness limitation

The hash mixer uses `s.char_at(i).to_i64()`. On the frozen seed,
`"A".char_at(0).to_i64()` returns 0, while `byte_at(0)` and `char_code_at(0)`
return 65. The numeric polynomial step gives 517350214, while the current
character conversion gives 517350149. Generation with exact Git LF input
bytes and two Windows seed versions reproduces the same header drift.

Current mixer output: HIR 371844268; AST 63731007; semantic 234834048.
An isolated byte-at experiment gives HIR 949155294; AST 908535153; semantic
688915752. Neither matches committed HIR 55988455, AST 106774408, semantic
45629152. The byte-at experiment was reverted; unrelated header churn was
discarded. The unchanged declaration schemas do not justify changing their
committed digest values in the import repair.

The full freshness selftest is not claimed passing under this authority;
the new negative fixture was exercised directly. Resolve and verify digest
semantics across interpreter/native authorities in a separate change. No full
bootstrap retry was performed after the focused repair.
