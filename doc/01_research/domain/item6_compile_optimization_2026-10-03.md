# Item 6 compile optimization: external research

Date: 2026-10-03. Primary sources retrieved on this date. Local application is
an inference, not a claim that another compiler's guarantees transfer to Simple.
Companion: [current-source research](../local/item6_compile_optimization_2026-10-03.md).

## Change propagation and durable identity

Rust's compiler guide explains that changed inputs do not necessarily change
query results. Red/green evaluation compares recomputed outputs before allowing
invalidation to continue. Persisted identities must be stable across sessions;
transient numeric IDs cannot safely identify cached entities. Fingerprints allow
comparison without eagerly loading every old result. [Rust compiler guide](https://rustc-dev-guide.rust-lang.org/queries/incremental-compilation-in-detail.html)

Application: Simple already separates content from export/ABI/initializer/provider
changes. Carry those per-module facts through the production route. Test a mixed
batch so a global “some public interface changed” flag cannot unnecessarily dirty
an unrelated private-edit consumer. Stable logical identity and semantic output
digest are distinct from source revision and physical checkout location.

## Multi-revision executable evidence

Rust's compiletest guide describes incremental tests that begin with an empty
cache and then compile successive revisions using the same incremental directory.
The test configuration can attach revision-specific expectations. [Compiletest](https://rustc-dev-guide.rust-lang.org/tests/compiletest.html)

Application: retain a real fixture/cache across setup, private edit, public edit,
and corrupt-cache phases. Each phase asserts the admitted dirty/reused sets and
result behavior. A fresh uncached run supplies the semantic oracle. Unit tests
remain useful but cannot substitute for this process boundary evidence.

## Cache identity and untrusted results

Bazel separates action-result mappings from content-addressed outputs. Its
documentation notes that environment differences, tools outside the workspace,
and concurrent input modification can cause cache problems; only configured
action environment variables enter the action definition. [Bazel remote caching](https://bazel.build/remote/caching)

Application: every supported target, provider, compiler, option, generated-input
and declared environment dimension must participate in Simple's admitted action
identity. Remote transport success is not admission. Verify returned payload
digests and local receipt bindings before reuse; preserve the pinned index as
graph authority. This reinforces existing requirements rather than proposing a
new remote service.

## Publication and failure recovery

SQLite's atomic-commit description distinguishes journal preparation, flushing,
database updates and the commit boundary. Correct crash behavior depends on
filesystem and storage assumptions; an apparently atomic operation is not an
automatic durability proof. [SQLite atomic commit](https://www.sqlite.org/atomiccommit.html)

Application: explicitly fault-inject before and after Simple generation pointer
publication, archive writes and receipt creation. Verify old or new complete
state, never mixed state, and test reader pins during cleanup. SQLite is prior
art for the failure model only: keep the selected pure-Simple CAS/journal and
PureDatabase projection owners rather than introducing SQLite as a dependency.

## Measurement design

The retained local NFRs already require pinned binary/source/toolchain and fixture
identity, repetition policy, elapsed distributions, RSS, counters and fallback
state. Separate cold indexing, warm compilation, no-op compilation and edit
compilation so initialization cost is not hidden in a cache-hit claim. Attribute
parse/type/lowering/codegen/link stages and filesystem operations before choosing
another optimization. No numerical speedup is inferred from these sources.

No additional feature option or NFR target is selected by this research. The
external sources support test and design refinements of the already retained
scope; production qualification remains an explicit unmet evidence obligation.
