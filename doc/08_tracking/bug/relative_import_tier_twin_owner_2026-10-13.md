# Relative imports lose physical sibling ownership across tier twins

Status: root source review PASS; native and SSpec checks UNRUN pending allocated,
qualified Pure-Simple execution. No runtime or release admission is claimed.

## Observed failure

The source-identical qualification2 CLI build used admitted Stage2
`4c2a777886ca37d66a5ae634ee02a4339107598122b6aa15d0b196c7735a9ada`,
frozen source `2ad4fd746ab9293777db2d9915c48791a0164863` and SCV
`c52b7f21afca9f3ffb2b47f836055845ea134227fbe34ad72bf3b6c860b72f05`.
It parsed and released all 2648 physical surfaces, then reported missing
`.object_mapper`/`.smf_cache` surfaces and resulting missing types in
`generation_sweeper`, `smf_cache_manager`, and `resource_lifecycle`.

Evidence: `/home/yoon/dev/phase3-whole-tests-evidence-20261013/loader-memory-astra/qualification2-cli-hir-fatal-diagnostics.json`.
The row also reported independent optimizer/bidirectional errors and timed out;
fixing these loader imports alone does not admit the CLI. The measured aggregate
peak was 4401780 KiB below its unchanged 5859375 KiB cap. No parser-memory code
repair was needed to reach this failure after MC/DC was correctly scoped away
from tool production; genuine test instrumentation remains required.

## Shared cause

`module_path_naming` collapses `99.loader/loader` for a file with no tier-root
twin, but retains the doubled spelling for `object_mapper` and `smf_cache`.
Thus `loader/generation_sweeper.spl` is `compiler.loader.generation_sweeper`,
while its physical sibling is `compiler.loader.loader.object_mapper`.

Both live HIR and the frozen surface resolver previously normalized the
importer before joining the relative tail. They looked for the root counterpart
`compiler.loader.object_mapper`. When absent this failed; when present it could
select the wrong implementation. The root mapper is a compatibility API with
i64 fields; the physical inner mapper has i32 fields and native mapping logic.
Changing these valid source imports to the root spelling would change ownership.

## Repair contract

The shared `module_relative_name_from_path` joins the relative tail to the
physical source directory before applying the existing module-name rule.
Frozen surface selection and its probe trace consume this rule. Live HIR uses
the same rule and receives the already-retained physical surface path for
logical-context calls. The duplicate live splice was removed so a wrong root
match cannot preempt the shared resolver. A missing physical sibling remains
a miss; it cannot fall back to the unrelated collapsed counterpart.
Lexical imports preserve the retained physical path before disabling the
module-level item-offset index. Their local item rows differ from module imports,
but their source owner does not. The first draft reset that index too early;
root review caught and corrected the resulting logical-context owner loss.

Absolute imports, public module names, definition mangling, and visibility
metadata are unchanged. Logical-only fixtures without source paths retain their
existing fallback. No filesystem probing, source scan, or registry-wide scan
was added. Relative work is linear in the path length and uses only the existing
target lookups. An early draft's additional context lookup was removed because
the current registry lookup is a scalar-array scan, despite its index-like name.
Resolver trace identity advances to `hir-module-surface-resolver-v3`
so old target decisions cannot masquerade as current witnesses.

## Verification awaiting authority

- `test/01_unit/compiler/common/module_path_naming_spec.spl`: physical siblings,
  reverse twin direction, parent dots, SCV/Windows paths, and unchanged non-relative inputs.
- `test/01_unit/compiler/hir/relative_tier_sibling_owner_spec.spl`: actual parser,
  frozen registry, and HIR lowering with distinct root/inner type owners; reverse
  imports, metadata privacy, parent imports, lexical aliases with a logical
  context and retained physical owner, and missing-inner negative cases.
- Existing `module_surface_resolution_trace_spec.spl` and
  `native_module_witness_facts_spec.spl`: current resolver identity.
- `test/fixtures/compiler/module_path_tier_identity/main.spl`: bounded native
  entry now includes four physical-relative cases, 15 checks total.
- Existing import-visibility, compiler/lib/MCP/LSP, runtime, and MCP native smoke
  checks remain required before production acceptance. None are claimed run.

Root reviewed the production changes, lexical-owner correction, regression
sources, and this diagnosis. Only patch whitespace was checked locally. Actual
execution, performance measurement, and rebuilt full-CLI qualification remain
pending; source review is not runtime or release admission.
