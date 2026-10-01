# Profile-switchable collections (implementation in progress)

An initialized local or class/struct field constructed directly as
`AdaptiveTextSet`, `AdaptiveTextMap`, `AdaptiveSet<K>`, or `AdaptiveMap<K,V>` can use
`@collection_algorithm("auto")`, `"linear"`, `"hash"`, or `"ordered"`.
The attribute changes that instance's physical storage. `auto` starts with
linear storage and can promote from live load or admitted prior measurements.
The declaration must call `new`, `with_profile`, or `with_site_and_target`
directly; text set/map declarations also accept `with_site` and
`with_attribute`.
An explicit algorithm takes precedence over prior measurements. Forcing hash
when the container policy disallows hash is an error. Generic keys currently
declare `Hash + Eq + Ord` bounds; aggregate-key native `Ord` dispatch still
needs a typed implementation and verification before general use. For an
`auto` generic map/set, a key that the native ordered comparator cannot handle
keeps hash or linear storage. A forced ordered insert fails with a diagnostic.
For `auto` under a no-hash policy, admitted prior size or lookup pressure can
select ordered storage. Without prior pressure, that policy starts linear.
An `auto` hash-backed instance also watches current-run collisions. If more
than one quarter of lookups in a bounded window encounter a high-collision
probe, it moves to ordered storage and keeps its values. A forced hash
attribute does not switch.

Capture a source workload for later replay:

```text
simple run app.spl --collection-profile-out=prior.sprof \
  --collection-workload=WORKLOAD_ID --collection-target=TARGET_ID
```

`--collection-profile-append` appends another admitted workload sample to an
existing matching file. The opt-in runtime channel captures peak collection
size, lookup/hit/miss counts, final distinct-key count, public materializations,
and hash probes/collisions when hash lookups occurred. Capture writes `.sprof`
v2 only after a successful run. The profile loader checks its schema, source,
workload, target, sample identities, and bounded record count.

To replay an earlier `.sprof` v2 collection profile during in-process source
execution, pass its file, workload, and target:

```text
simple run app.spl --collection-profile=prior.sprof \
  --collection-workload=WORKLOAD_ID \
  --collection-target=TARGET_ID
```

The profile's module identity must equal `sprof_source_module_identity(app.spl)`,
which hashes the project-relative source path and source text while canonicalizing
valid `@collection_algorithm` arguments. An algorithm-only edit retains the
identity; other source edits do not. Relative and absolute path spellings under
the same working directory share a key. An optional `--collection-module=ID`
is checked against that current identity. `WORKLOAD_ID` must equal the profile
header value, and `TARGET_ID` must equal the target on collection samples.
The loader rejects stale,
malformed, or ambiguous profiles before running the program. The compiler
parses source with a prepared site index and embeds matching prior counts in
attributed initializers. It bypasses a cached SMF artifact for that run and
clears the index afterward. This mode rejects execution delegated to another
binary because the prepared parser state would not cross that process
boundary. Use a source matched self-hosted Simple runtime configured for
in-process execution.

The same admitted profile can be embedded into an LLVM native build:

```text
simple native-build --backend=llvm --entry-closure --entry app.spl \
  --source src/lib --output build/app \
  --collection-profile=prior.sprof \
  --collection-workload=WORKLOAD_ID --collection-target=TARGET_ID
```

The native cache and final-artifact warm receipt bind to the profile bytes,
workload, and target. A profile or source entry changing during compilation is
rejected. The initial storage explanation is available through
`simple optimize app.spl --explain-collection-plan --profile=prior.sprof
--collection-workload=WORKLOAD_ID --collection-target=TARGET_ID`.

These paths have source-level specs but have not run on an admitted,
source-matched pure-Simple compiler. Typed CollectionPlan-to-MIR lowering,
arbitrary generic key ordering, all collection/join measurements, and
cross-target performance evidence remain open. The explanation reports
`guard.typed_mir=unconnected` until that compiler path is implemented.
