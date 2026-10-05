# Source snapshot cost — local research

<!-- codex-research -->
Date: 2026-10-05. Source review based on release_temp 6ff49761c0f.

Research only. No compiler execution, cache mutation, source edit, or active
bootstrap modification was performed for this follow-up.

## Evidence boundary

Hello source is 65 bytes, one compiled module. The existing SCV snapshot has
16,357 entries. Cranelift cold-SCV compile: 361.635 s, 3,376,680 KiB process-tree
peak RSS; subsequent LLVM existing-SCV compile: 141.597 s, 3,959,476 KiB. Both
report frontend 0 hits/1 miss/1 parse and HIR 0 hits/1 miss/1 store. Therefore
the second run is SCV-warm, not a warm artifact-cache benchmark. Different
backends prevent a controlled speed comparison. Driver progress ends at
418 ms/470 ms; those counters omit most end-to-end work.

Existing filesystem timestamps bound, but do not instrument, these intervals:

| Run | Invocation to first frontend artifact | Object to executable |
|---|---:|---:|
| Cranelift | 307.689 s | 41.509 s |
| LLVM | 70.352 s | 49.534 s |

Cranelift snapshot publication is 295.085 s after invocation. These intervals
contain all intervening work; do not label them exclusive snapshot/link times.
No phase-correlated RSS samples were retained, only aggregate peaks.

Evidence root: `C:/Users/user/.simple/worktrees/simple/runtime/windows-restart-20261004/qualification-916be-hello-{cranelift,llvm}1/`.
Use `results.json`, `<backend>/hello/compile.log`, `compile.rss.env`,
`cache/build_cache.sdn`, and `cache/warm-artifact-v2/*.receipt`.

## SPipe and knowledge selection

`SPIPE_HOME` and `SPIPE_WORKSPACE` are unset. Project `.spipe/common` and named
home defaults are absent. Configured legacy common `.spipe/spipe` is valid;
canonical `node scripts/find-spipe.mjs --agent-guide` resolved it. Package is
`@simple-lang/spipe` 0.2.0; checkout and project gitlink both equal
`0a00354eeea87ab7a74ef6e1aa3b8d5756bc1b75`. Common index, wiki/skills indexes,
plugin bootstrap, ownership setup, and scope-resolution guidance were read.
No optional company/organization/user/host scope was selected or probed.

`doc/00_llm_process/knowledge_registry.sdn` has no exact source-snapshot-cost
feature route: retain this research gap, not a fabricated match. Longest prefixes:

- `src/lib`: `runtime_memory_io`, `layer_base/runtime_memory_io/skill.md`, mdsoc_plus.
- `src/compiler`: `compiler_pipeline`, `layer_base/compiler_pipeline/skill.md`, mdsoc.
- `src/app`: `app_editor_tooling`, `layer_base/app_editor_tooling/skill.md`, mdsoc_plus.

Root should persist these under its chosen feature's knowledge_selection.sdn.

## Current owners and costs

1. `src/app/compiler_entrypoint/source_authority.spl:106`,
   `compiler_source_authority_acquire_v1`: refresh inventory, acquire snapshot,
   then validate authority. `inventory_roots_v1:123` admits whole src/test event
   families independently of exact snapshot selectors; cold init adds both.
2. `src/app/compiler_entrypoint/inventory_events.spl:311`,
   `compiler_inventory_git_events_v1`: cold uses one tagged ls-files listing;
   warm uses captured HEAD, optional committed diff, and porcelain status.
   `_compiler_inventory_refresh_locked_v1` validates journal prefix, membership,
   and immutable CURRENT under locks. An unchanged-pointer fast path already
   avoids apply/encode/publish/readback; do not reinvent it.
3. `src/lib/scv/compile_snapshot.spl:150`,
   `scv_compile_snapshot_inventory_entries_v1`: reads current admitted inventory,
   filters logical roots, and checks physical containment of selected entries.
4. `scv_compile_snapshot_acquire_v1:378`: constructs planned manifest/revision
   and reuses a validated existing destination before materialization. Identical
   snapshot reuse already exists. Broad roots, not entry closure, define this
   view. `src/app/io/_CliCompile/native_build_snapshot_roots.spl` preserves explicit
   roots; default adds app/lib/compiler/os/plugins and the entry parent. The
   Hello wrapper explicitly passes similarly broad roots.
5. `scv_compile_snapshot_materialize_source_unscoped_v1:322`: read+hash source;
   publish or verify existing chunk; write+hash-verify destination; reread+hash
   source for drift. This is real multiple I/O/hash work per selected file,
   but the receipts do not quantify its share. `materialize_source_v1:359`
   already scopes scratch and retains only a compact row/result.
6. `scv_compile_snapshot_open_v1:235`: rereads/hashes/parses the full manifest.
   `source_authority_validate_v1:84` reads inventory and manifest again for
   binding. Parent parse-closure publication opens authority; closure freeze
   opens/inherits it again; selection publication reads its inventory; worker
   `native_entry_closure_owner.spl:82` opens the snapshot. These call paths
   establish repeated validation opportunities, not measured call counts.

## Existing design, not production authority

`doc/01_research/local/compiler_semantic_cache_daemon_virtual_summary_2026-09-01.md`
and `doc/04_architecture/compiler_semantic_cache_manager.md` already design
immutable SourceBlob/CompileSnapshot CAS, full SemanticReadSet (including
negative candidates), and a checksummed authoritative journal with a rebuildable
database projection. The architecture explicitly calls itself proposed and
retains shadow-only activation gates. Do not treat design text as a deployed
fast path.

`src/compiler/10.frontend/snapshot/compile_snapshot_freezer.spl` implements a
pure freeze state machine (`freeze_compile_snapshot_v1:358`) over same-handle
observations. Observations are expressly not security/publication authority.
`resolution_witness_v1.spl` binds ordered candidates, absent higher-priority
candidates, physical identity, parent generations, content and symlink chain.

## Options for root's research/options artifacts

- **S: narrow explicitly known fixture selectors.** Uses existing exact-root
  snapshot mechanism; low implementation effort and smaller materialized view.
  Does not eliminate cold whole-family event admission or general import
  closure requirements. Regression: sibling/relative import coverage and no
  fallback to live checkout.
- **M: reuse one validated immutable admission per request/epoch.** Avoid repeated
  manifest decoding and row-map construction while keeping fresh handle-bound
  source checks. Bind memo to full source owner, generation, manifest, revision,
  entry/policy/provider identities and lifetime. Never trust environment strings
  as standalone evidence, skip child verification, or weaken drift checks.
- **L: dependency-selected immutable CAS views.** Reuse the existing designed
  frozen-source/read-set authority, materialize only resolved dependencies.
  Must include negative resolution, directory membership, generated inputs,
  traits/impls/extensions, macros, AOP selectors, target/config/provider changes.
  An imported filename set alone is unsound. Requires production host authority
  integration and differential admission; not a quick warm-cache shortcut.

Do not replace hashes with mtimes, hardlink mutable checkout files into frozen
snapshots, or introduce lazy fetches from current source after admission.
Existing CAS blobs also require ownership/integrity checks before reuse.

## Tests and measurement

Existing tests: `test/01_unit/lib/scv/compile_snapshot_source_roots_spec.spl`,
`compile_snapshot_alias_selection_spec.spl`, `compile_snapshot_reclamation_spec.spl`,
`test/01_unit/app/compiler_entrypoint/source_authority_spec.spl`,
`test/05_perf/scv/compile_snapshot_resource_profile_spec.spl`,
`test/05_perf/scv/git_inventory_warm_workload.spl`.

Add negative-candidate creation, untracked add/delete, rename, same-size edits,
symlink escape/case alias, CURRENT advance during parent/child transfer,
corrupt/missing immutable blob, concurrent publication, generated input/target
change, and nested-scope refusal cases for any new reuse path. Measure unchanged,
single-file edit, dependency edit, and cold population separately; retain p50/p95,
peak/steady RSS, bytes hashed/copied, manifest decodes, process launches, and
actual reuse counts. The <0.1 s target cannot be claimed from these observations;
startup/protocol and final runtime/link overhead must also fit its scope.

## Six-product generator preparation observation (2026-10-05)

The active diagnostic packet `six-products-current-proven-transport1` prepares
six private tool roots before producing the six requested subsystem test binaries.
All six generator commands select the same
`src/app/compiler_subsystem_product_generator/main.spl` entry, frozen Phase 2
producer `2b83155910336e56ec8b663c3d3e7d3ceb9c61b60fa98182163f9670ff044c33`,
and source revision 916be6. Three use LLVM and three use Cranelift; output paths,
private source roots and private caches differ. Backend-specific product coverage
must remain six distinct products even if helper preparation is later shared.

A bounded process/log audit found six live generator compiler processes, each
adding approximately 21-23 CPU seconds during observation and initially retaining
about 1.44 GiB RSS. They were materializing SCV snapshots in their private roots;
no subsystem enumeration had started. All six source-inventory steps had already
completed with exit zero and closed process trees. These observations show
replicated helper preparation, not an exclusive timing attribution or a proven
cache defect. The current frozen commands and caches were left untouched.

A future optimization can investigate one immutable generator/verdict helper
artifact per complete producer/source/backend/target/runtime/options key, with
separate per-product requests and results. Cross-root equivalence must be proved:
source authority, generated inputs, root-sensitive paths and dependency policy
cannot be omitted from the key merely because entry text matches. Single-writer
publication, validated readers, corruption/drift rejection and bounded memory
must be tested alongside cold/warm latency. This is supporting evidence for
TODO 347; no new sharing implementation or design option is selected here.
