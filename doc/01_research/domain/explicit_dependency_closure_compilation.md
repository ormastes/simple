<!-- codex-research -->
# Explicit Dependency-Closure Compilation — Domain Research

## Research question

How can Simple compile one requested package/module and its dependency closure
without recursively scanning unrelated source trees, while preserving exact
semantics, hermeticity, incremental correctness, and bootstrap operation?

## Java compiler behavior

The official `javac` documentation distinguishes command-line source files from
additional sources found through a package-oriented source path. It resolves a
referenced type by its package/module location; a found source may be compiled
implicitly. Package paths are searched in declared order and the first matching
file shadows later matches. This is direct name-to-path lookup, not a request to
enumerate every source under each root. The important Simple analogue is an
ordered, identity-bound resolver plus explicit handling of implicit compilation,
not Java’s timestamp preference. Source/class ambiguity must be fail-closed or
policy-bound in Simple. [Oracle `javac` command](https://docs.oracle.com/en/java/javase/25/docs/specs/man/javac.html)

## Go package compilation and export data

The Go compiler compiles one package from the files named on its command line.
Its output carries exported type information so a client package can compile
from the direct dependency’s compiled output without reading that dependency’s
dependencies. This closely matches the requested package-summary model.
[Go `compile` command](https://go.dev/cmd/compile/)

Go’s compiler documentation describes “deep” export data: a direct import’s
summary includes enough declaration information for referenced indirect types.
Indexed encoding permits lazy decoding. Deep summaries simplify distributed and
hermetic builds but can duplicate common API data; shallow summaries are smaller
but require random access to transitive metadata. Simple should begin with a
bounded deep summary for public type completeness, plus an index so large records
can be decoded by section. [Go compiler export data](https://go.dev/src/cmd/compile/README)

Go modules also demonstrate graph pruning and lazy loading: comprehensive direct
requirements let commands avoid loading the complete module graph unless a
missing package forces it. This supports making direct imports complete and
authoritative in Simple metadata. [Go modules reference](https://go.dev/ref/mod)

## ABI-aware incremental Java builds

Gradle analyzes class dependencies and recompiles affected classes. Its compile
avoidance distinguishes ABI-compatible method-body edits from public API edits,
and its class analysis is persisted with build-cache outputs. It also documents
cases that require broader invalidation, including constants and annotation
processors. The Simple analogue is a public ABI digest plus explicit metadata
for macro/AOP/generated-code and initializer effects; hidden processors are not
acceptable. [Gradle performance guide](https://docs.gradle.org/current/userguide/performance.html),
[Gradle Java plugin](https://docs.gradle.org/current/userguide/java_plugin.html)

Bazel's `ijar` strips executable method bodies, private members, debug data, and
other compile-irrelevant content from Java archives, retaining the package-level
interface needed by downstream compilation. That is the closest header-jar
analogue for Simple's package TLDR/SMF split: downstream actions should depend on
semantic/export data rather than the producer archive's raw implementation
bytes. Package-private API cannot be discarded merely because it is not public.
[Bazel interface JAR design](https://github.com/bazelbuild/bazel/blob/master/third_party/ijar/README.txt)

Java module metadata (`module-info.java`/compiled module descriptors), classpath,
module path, upgrade module path, and source path create distinct lookup and
visibility namespaces. Simple likewise needs variant/toolchain-bound catalog
namespaces and must preserve resolver order/evidence rather than treat a package
name as globally unique. [Oracle `javac` command](https://docs.oracle.com/en/java/javase/25/docs/specs/man/javac.html)

## Go action IDs and archive cache

The Go tool records an action ID derived from inputs separately from a content ID
derived from the produced archive/binary. Installed package archives can serve as
cache entries; consumers use content IDs to avoid hashing large artifacts and to
support reproducible bootstrap convergence. Simple should retain the same
separation among action identity, source content, semantic export identity, and
archive content. [Go build ID implementation](https://go.dev/src/cmd/go/internal/work/buildid.go),
[Go build cache package](https://pkg.go.dev/cmd/go/internal/cache)

## Hermetic dependency graphs

Bazel distinguishes declared dependencies from actual dependencies and requires
the actual graph to be a subgraph of the declared graph. That is the right
fail-closed rule for Simple: every source, generated input, runtime provider,
initializer, macro/AOP input, tool, and configuration read must appear in the
summary/action witness. [Bazel dependencies](https://bazel.build/concepts/dependencies)

Skyframe records dependency reads and rebuilds the reverse transitive closure of
changed inputs. Change pruning can stop propagation when a recomputed value is
unchanged. It also forbids untracked filesystem reads by graph functions because
they make incremental results unsound. Simple’s package loader should likewise
obtain files and metadata only through an instrumented catalog/admission owner.
[Bazel Skyframe](https://bazel.build/versions/8.5.0/reference/skyframe)

Bazel hermeticity binds tools and inputs so the same declared inputs produce the
same output. Simple summaries therefore need compiler/options/toolchain/provider
identity, not only source and import digests. [Bazel hermeticity](https://bazel.build/concepts/hermeticity)

Bazel remote caching separates an action cache from a content-addressable store.
The useful Simple boundary is immutable action-result/summary/archive blobs;
mutable local catalog pointers, event cursors, leases, and source-snapshot
admission must not be delegated to the remote cache. [Bazel remote caching](https://bazel.build/remote/caching)

## Incremental graph algorithms

Rust’s red-green query model records exact computation dependencies, reuses a
cached value only when its inputs are green, and stops propagation when a
recomputed result is unchanged. This is a useful later refinement beneath the
package boundary, but it is substantially larger than the requested discovery
optimization. [Rust incremental compilation](https://rustc-dev-guide.rust-lang.org/queries/incremental-compilation-in-detail.html)

“Build Systems à la Carte” separates scheduler, rebuilder, store, and dependency
model and explains early cutoff: dependents need not rebuild when an affected
task recomputes to the same value. It also warns that untracked tool inputs break
correctness. [Mokhov, Mitchell, and Peyton Jones](https://ndmitchell.com/downloads/paper-build_systems_a_la_carte_theory_and_practice-21_apr_2020.pdf)

The Pluto follow-up on scalable incremental building argues that rebuild cost
should scale with change impact rather than total graph size. A changed-file-led
bottom-up traversal avoids loading the entire graph, while a mixed traversal
handles dynamic dependencies. This supports a trusted dirty-set input plus
metadata-guided forward closure and reverse-reference invalidation in Simple.
[Konat, Erdweg, and Visser](https://gkonat.github.io/assets/publication/scalable_incremental_building-ase18.pdf)

## Design implications for Simple

1. **Compilation unit:** package/module SCC, not arbitrary repository tree.
2. **Lookup:** canonical module catalog and ordered direct probes, never recursive
   discovery in the requested-module path.
3. **Header:** self-sealed, versioned package SMF combining Go export depth with
   Java-class-like identity and ABI information.
4. **Correctness:** declared metadata must cover every actual input; untracked
   reads are errors.
5. **Incrementality:** trusted dirty set drives source opening; interface digest
   and typed reverse facts drive propagation and early cutoff.
6. **Security:** metadata never authorizes itself. Catalog generation, canonical
   path, source-change witness, content digest, producer/toolchain identity, and
   artifact digest are independently admitted.
7. **Cycles:** condense import graph into deterministic SCCs and publish each SCC
   atomically.
8. **Fallback:** without trustworthy metadata/change evidence, perform a bounded
   source-led closure from explicit roots or fail closed; never widen silently to
   an unrelated full-tree scan.

## Complete Java/Go/Bazel gap comparison

| Prior-art capability | Required Simple equivalent | Current gap |
|---|---|---|
| `javac` package/module lookup | Ordered direct catalog resolver | No persistent authoritative package lookup |
| Java sourcepath implicit compilation | Bounded dirty/missing package source open | Reachable source is still opened to discover imports |
| Class/interface/header JAR | TLDR + complete package SMF/export record | SIF/SMF do not yet form a package discovery header |
| Java module descriptors | Variant/toolchain/provider visibility metadata | Resolution inputs remain fragmented/implicit |
| Go one-package compilation | Package/SCC action | Driver still compiles source-led aggregate closure |
| Go deep indexed export data | Lazy indexed public type sections | No complete package export decoder/producer |
| Go package archive/build cache | Immutable package archive CAS | Existing caches lack package product authority |
| Go action ID/content ID split | Action/content/semantic/archive identities | Primitives exist but are not composed at package level |
| Go build tags/generate | Explicit variant and generator actions | Generated/config inputs are not one graph authority |
| Bazel declared graph | Actual reads subset of package metadata | No post-freeze access broker enforcement |
| Skyframe reverse edges/early cutoff | Typed package reverse facts/change pruning | Facts exist; package scheduling and cutoff are missing |
| Bazel parallel action DAG | Deterministic bounded SCC workers | No package-level scheduler |
| Bazel remote AC/CAS | Immutable blob-only remote boundary | No package readmission protocol |
| Rust red-green reuse | Independent semantic dimensions | Current invalidation begins from enumerated sources |
| Hermetic repository snapshot | Non-mutating SCV build freeze | No landed compiler integration; live reads remain possible |
| Crash/restart build graph | Atomic generations, leases, recovery | Pieces exist separately, not end-to-end |
| Reproducible diagnostics/artifacts | Canonical schedule and path-free identities | Not proven for metadata-led parallel packages |

## Domain conclusion

The strongest primary design is not merely “cache parsed imports.” It is a
hermetic package catalog plus complete package-header metadata, with a bounded
source fallback and exact invalidation. Go supplies the package/export-data
shape, `javac` supplies direct package-path resolution, Gradle supplies ABI-aware
compile avoidance, and Bazel/Rust/build-system research supply dependency and
invalidation correctness.

## Addendum — transparent, read-only Git event integration

Official Git documentation exposes an important safety constraint. `git status`
normally refreshes and writes index stat data; background tools should use
`git --no-optional-locks status`, equivalently `GIT_OPTIONAL_LOCKS=0`, to avoid
that side effect and lock contention. Therefore automatic compile snapshotting
must force no-optional-lock mode for every Git inspection and must reject any
adapter command that can update the index. [Git status background refresh](https://git-scm.com/docs/git-status.html),
[Git `GIT_OPTIONAL_LOCKS`](https://git-scm.com/docs/git/2.52.0)

`git ls-files` exposes the sorted index/worktree inventory and NUL-delimited
machine output. It is a useful read-only reconciliation input for tracked paths,
but untracked discovery can search directories; the compiler may not hide that
cost as package discovery. Event overflow or cold untracked state therefore
needs an explicit inventory-resync receipt and bounded policy. [Git `ls-files`](https://git-scm.com/docs/git-ls-files)

Git post-checkout and post-merge hooks can notify tools after worktree-changing
operations, but hooks are not complete observation: edits, failed operations,
and environments without installed hooks still exist. Hooks may accelerate
SCV inventory refresh, never become sole correctness authority. [Git hooks](https://git-scm.com/docs/githooks/2.46.0.html)

`git hash-object` writes Git object storage only with `-w`. Automatic SCV freeze
must not use `-w`; in this design, raw source content is hashed and stored only
inside the dedicated compiler/SCV cache. [Git `hash-object`](https://git-scm.com/docs/git-hash-object)

The resulting rule is: Git events are quiet freshness hints, read-only Git
porcelain/plumbing may reconcile tracked inventory with optional locks disabled,
and the immutable source bytes, inventory, leases, and receipts are owned only
by the ignored SCV build-cache namespace. No hook or compile invocation may
commit, push, rewrite index/refs, remove locks, or mutate history.
