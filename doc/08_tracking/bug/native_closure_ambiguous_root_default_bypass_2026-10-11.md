# Native outer closure loses source-root ambiguity

Status: source correction and native fixtures authored; native qualification
pending. This is distinct from the proven null callback dispatch recorded in
`source_root_fallback_null_callback_2026-10-11.md`.

The source audit of aggregate `c2a88e77ec2847e63cdc540e726ed38f11e6a88b`
establishes this path:

1. `native_build_closure.spl:266` resolves numbered directories through
   `_driver_try_numbered_entry_import_rel`, whose compatibility text result
   collapses `Ambiguous` to empty at `driver_source_loading.spl:997`.
2. The outer `_nb_resolve_segs` loop continues to a later valid source root
   (`native_build_closure.spl:272–286`) and queues that default module.
3. The driver's closure loop can find that logical module already loaded
   (`driver_source_pipeline_loading.spl:1019–1028`) and skip the tri-state
   selected-root check. The direct-call repair in `b848f700953` does not fix
   this earlier authority loss.

This is a causal source finding, not a claimed native reproduction. Existing
composition precedence specs exercise the resolver directly; the retained CUDA
audit reports integrated filesystem/closure qualification pending. No existing
native ambiguity rejection PASS was found or inferred.

The correction carries the existing `SourceRootResolutionV1` through the two
private outer resolver functions and exposes the existing checked numbered
resolver to that caller. Exact path checks, ordered roots, root-name stripping,
standard-library tiers, relative imports, and terminal-name fallback order are
retained. Both uncached BFS lookup sites reject `Ambiguous`, emit
`SOURCE_ROOT_AMBIGUOUS`, and return an empty failed closure before cache insertion,
queue admission, or warm-candidate publication. Successful/Missing cache values
remain text. No global failure flag or diagnostic-only helper is introduced.

The ordinary caller rejects an empty closure before compilation
(`compile_targets.spl:1291`); the parse-shard publication path revalidates entry
membership (`native_entry_closure_receipt.spl:152`) and rejects an omitted entry.
The patch uses these existing failure contracts and does not disable admission.

`test/fixtures/compiler/source_root_authority_native/README.md` defines four
native cases using the existing competing overlay, a real later default, and
an earlier exact owner. Negative success requires the named ambiguity diagnostic,
nonzero exit, and absent output; crashes or unrelated errors do not qualify.
The two positive controls must execute and print their distinct owner values.
No native build or test was run for this source-only correction. Full gates and
release admission remain pending the coordinated producer and queue execution.
