# Target-bound macro category production

Status: architecture-approved source implementation under review; no runtime qualification.
Requirement: REQ-DTA-A1/B3. The parent owns the actual phase-2 capture and final
PackageInit aggregation hooks. This lane owns the frontend capture/projection API.

The existing module artifact emitter is a host-profile/source-bound companion
producer. Its record is not evidence of the current target, compiler image or
source generation. The new path will consume actual full-parse macro pools while
that parse owns them and will not recover authority from an older companion.

Source owner: `compiler.frontend.cache_artifact.macro_category_projection_v2`.

- `MacroCategoryInputV2`: existing `MacroModuleSourceV1`, existing guard evaluations,
  source identity/digest, target and cfg receipt digests, policy and executing-image
  digests, parent-owned `DirectorySourceEpochV2` (driver identity + generation),
  and explicit resolved imports (all/selective and original/visible alias names).
  This is typed data with trusted caller provenance, not an unforgeable token.
- `macro_category_capture_v2(...)`: called immediately after successful full parse;
  verifies source/target receipt, scopes the existing preprocessor evaluator to the
  receipt target, captures current macro pools, and restores previous state on every
  returned path. It does not yield, parse another file, or retain parser AST nodes.
- `macro_category_project_all_v2(inputs)`: validates a bounded same-generation graph,
  resolves imported definitions from current inputs only, and projects with the
  existing macro projector. Deterministic Kahn ordering detects dependency cycles;
  a missing needed import, mixed target/provider/epoch or ambiguous identity refuses
  the graph rather than inventing a complete empty imported definition table.
- `MacroCategoryProjectionV2`: source/variant binding, existing real module macro
  projection, definition-key root, actual input root, effect surface and category
  root. Source epoch is an admission discriminator, not part of the semantic digest.

A file with neither invocations nor nested macro reads does not need unrelated
ordinary imports to compute its local macro category. Known-empty still requires
actual successful full parse. Guards use the exact target policy and existing
condition evaluator, not the process host fallback. Imported records must share
the current source generation, target, policy and executing-image identity.

The existing projector's CTFE read root is a placeholder; such a definition cannot
be declared complete by this path until an actual read-closure owner is supplied.
The existing inactive-definition scanner supports only single-line headers;
unsupported inactive syntax must be explicitly unavailable, not silently absent.
The implementation must retain these limitations in tests and diagnostics rather
than marking the whole macro feature complete.

Planned tests cover saved preprocessor state restoration on success/error, target
selection different from host, fresh empty parse, local definitions and uses,
imported resolution under changed input order, mixed-generation refusal, missing
imports, cycles, duplicate identities, unsupported effects and bounded inputs.
All tests remain unrun until a separately admitted native pipeline is available.

The parent owns source-lineage allocation at `load_sources_impl` and map reset.
The later AOP lowering epoch and zero/unrelated diagnostic generations are not
substitutes. Epoch correlation does not authenticate current source or compiler
identity; those remain separately checked inputs.

Implementation checkpoint: the frontend owner and twenty-one authored scenarios exist.
The graph uses a 128-module limit, the existing shared payload/item budget across
all captured inputs, and the existing macro-edge count limit. Current imports
are resolved deterministically with Kahn traversal; no disk companion is read.
The parent must require actual parser initialization generation to advance across
the successful full parse, because a cached AST does not prove current macro-pool
ownership. The parent must also promote the entire compact input graph before
ending parser scratch. Production hooks and native execution remain pending.

The old source adapter body was extracted verbatim into
`macro_module_source_from_scan_v2`; the legacy wrapper still computes its original
scan and delegates. A source-level exact-body comparison passed. New capture
computes one target-scoped scan and checks inactive macro header coverage against
its real guard/evaluation/definition records. Code/data/init exclusion rows are
not used as proof that macro declarations were captured. All twenty-one scenarios
remain authored and unrun.

Import bindings now use `MacroCategoryImportV2` and
`MacroCategoryImportNameV2`; ordinary import paths alone are insufficient. The
existing projector owns `MacroImportBindingV2(visible_name, origin_def_id)` and
the new checked `project_macro_module_bound_v2` entrypoint. Candidate lookup,
nested reads, diagnostics and the namespace/absence root consume this binding
context. Canonical definition entries, IDs, bodies and keys are never renamed.
Legacy wrappers pass no binding context and preserve the existing all-public
lookup policy. The new API rejects ambiguous visible names or unavailable
origins. Actual parent import-resolution policy must decide namespace exposure;
an empty parser item list must not automatically imply an all-symbol import.

The unchanged legacy adapter tail has SHA256
`eb9e50224e5b2a05d4d918bdbc5f091bce5af4bcb3faaef6021c2d36b6431b8d`;
source comparison confirmed exact equality before/after extraction. This is not
an executed compatibility test. The total graph budget is returned and explicitly
reassigned between inputs, so enforcement does not rely on aliasing a mutable
class across calls.

Astra found two source availability/coverage defects before acceptance: the
legacy key projector recurses and performs quadratic name scans, and its inactive
header scanner accepts a complete parameter list with an unfinished contract.
V2 now limits capture to 64KiB/2048 lines and 256 macro rows, validates complete
single-line inactive headers, and gates legacy projection with iterative local
dependency depth (maximum32), per-module cardinality limits and a graph-wide
one-million-unit conservative candidate/namespace work budget. Long-chain,
large-binding and multiline-contract refusal specs are authored, not executed.
Legacy V1 projection policy is unchanged.

V2 overlays actual `macro_fact_def_visibility_at` values onto active definitions:
public remains public, private remains private, and scoped visibility is unavailable
until its namespace policy is represented. Admitted plain inactive declarations
retain the parser's private default; prefixed inactive declarations are refused
because the legacy scanner cannot retain them. The legacy companion remains
unchanged. Actual-parse visibility and prefixed-inactive regression specs are UNRUN.
