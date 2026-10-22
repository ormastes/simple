# Phase3 ordinary native entry/cache review candidate

Status: authored, native qualification pending. Base f07dfb4707c046345321424ddb67099defe6a96e. This is a narrow review candidate, not acceptance of all12 feature groups.

The candidate always parses current full source, performs existing type checking/HIR/MIR processing and preserves current capsule/object/receipt checks. It retains compact source interface and resolution facts before streaming reclaim, then combines them with current MIR/layout/config. Textual interface extraction alone never authorizes imported body omission.

`--emit-entry-object` is a new explicit delivery intent. It requires prepared imported objects; an imported miss fails before worker start. Exactly one canonical requested entry object must survive all module outcomes, non-vacuity and cold-native persistence gates. The action copies its bytes through retained opaque handles into an immutable generation output, verifies SHA equality, fsyncs requested object and directory, then returns before relocatable or final link. Original capsule receipts keep their original paths. Matching existing output is idempotent; different existing bytes refuse, so callers use generation output paths. Existing `--emit-object` aggregate behavior remains separate.

Executable-only no-op eligibility prevents a program receipt satisfying an object request. The canonical module environment projection normalizes executable/entry final delivery intent only; full action environment capture and every other field remain bound. Other output scopes stay conservative.

Acceptance scenarios (authored, UNRUN):

- Current entry-body change reaches actual provider cache-hit branch, preserves provider path/bytes/receipt and matches isolated frontend/HIR/native cold execution.
- Signature/body/generic/default/constant/initializer/layout/target/negative-import/overload/impl/aspect changes match cold output or genuine unsupported diagnostics; invalid current source cannot publish stale output.
- Missing/corrupt native bytes or receipts rebuild safely on ordinary actions.
- Entry-only action yields real Linux ELF ET_REL, preserves imported bytes, reports only one rebuild, and refuses missing imported ObjectReady without recreating it.
- Module environment capture preserves codegen/tool differences, rejects duplicate capture and keeps the full action intent distinct.
- Direct-argv link transport preserves two80KiB arguments, metacharacters, empty strings, child exit/stderr and explicit truncation; real host cc behavior is tested separately.

Executable specs: `test/03_system/compiler/incremental/object_reuse_driver_spec.spl`, `native_link_transport_spec.spl`, and four driver unit specs in this package. Manuals: matching paths under `doc/06_spec/03_system/compiler/incremental/`.

No metrics sink is installed by this slice. Native timing/counter/tree measurements and the100ms target remain unavailable, never zero or PASS. No Rust/test seed fallback is authorized.

Remaining12-feature ledger is preserved:01 header summary/native ABI handoff pending;02 managed epoch qualification pending;03 shared parsing/receiver completeness pending;04 this scoped cache candidate pending native acceptance;05 managed artifact service pending;06 runner recovery pending;07 edit tracking pending;08 observer/closed latency receipt and realistic cohort pending;09 sealed archive emitter and complete MIR decoder pending;10 full compiler/app ObjectReady outcomes pending;11 process parallel native qualification pending;12 installed measurement coverage pending. Existing authored owner bundles remain in their respective ignored lanes and are neither deleted nor marked DONE.

## Admission-to-publication replacement guard

The capsule validator returns the original successfully authenticated SHA and byte count. Cache-hit admission and codegen parent postprocessing retain those exact values through the entry cutoff. The cutoff never recomputes a digest to grant authority. Its scoped opaque source descriptor hashes/copies against the retained original digest and size, then verifies/fsyncs the requested output and parent directory. No descriptor crosses the driver’s fallible phases.

The authored native_entry_object_publication_spec performs a deterministic filesystem race: after original successful capsule admission it replaces the object and issues a matching replacement receipt, proves that new receipt would validate independently, then requires publication with the retained original authority to reject and leave no output. Equal admitted bytes remain idempotent. This boundary fixture is not native codegen evidence; the separate actual entry native scenario remains required. All runtime cases remain UNRUN.

The existing retained-descriptor receipt API supports whole-file offset-zero reads capped at 64 MiB, rather than arbitrary-offset chunk reads. Entry publication uses that actual contract, with one bounded transient byte array, and rejects larger objects. Close success is zero; fsync success is one. This draft does not claim an NFR RSS target. Cached and new canonical object/receipt handles and their directory are fsynced before requested output publication.
