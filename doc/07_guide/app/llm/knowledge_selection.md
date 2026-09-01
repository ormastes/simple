# Deterministic Feature and Layer Knowledge Selection

Before implementation, resolve the exact feature ID in
`doc/00_llm_process/knowledge_registry.sdn`, then longest-prefix match every
planned or changed `src/**` path. Load the feature-group base and exact feature
expert, plus every matched layer-base and layer expert. Deduplicate and order
paths lexically so all pair-programming participants use the same bundle.

Missing feature IDs, missing layer routes, equal-length competing prefixes, and
empty path lists fail closed. Record registry version, feature, selected paths,
source-to-prefix decisions, and architecture profiles in
`.spipe/<feature>/knowledge_selection.sdn`. Implementation and verification
consume that receipt; they do not reconstruct selection heuristically.

The Simple selector is `std.common.llm.knowledge_selector`. Paths under
`src/os/kernel/**` and `src/os/drivers/**` are always `mdsoc_only`; a registry
entry attempting MDSOC+ there is rejected. Userland services/apps may select
`mdsoc_plus`. Private wiki material may attach by stable ID but cannot replace
the public registry or weaken architecture policy.
