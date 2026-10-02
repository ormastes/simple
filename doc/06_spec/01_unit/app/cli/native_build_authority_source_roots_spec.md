# Native-build parent source selection

Executable: `test/01_unit/app/cli/native_build_authority_source_roots_spec.spl`.
Native execution and SPipe doc generation: pending. No passing result is claimed.

Named, equals-form and positional entries must yield the same complete worker
default roots plus the exact entry. Backend and output values must not become
positional entries.

Explicit source roots remain finite and unchanged. Collection profile,
workload and target option values must not be misclassified as entries.

An unbounded root-level entry, a missing entry value, source-only arguments
and an entry outside the checkout must be rejected with empty selection.

Pinned-generation, drift propagation and incomplete-authority rejection are
covered separately by `test/01_unit/app/compiler_entrypoint/source_authority_spec.spl`.
