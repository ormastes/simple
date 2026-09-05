<!-- codex-research -->

# Domain Research: Minimal-Bootstrap, Configuration-Composed Dynamic Architecture

> Status: domain rationale extracted from user-supplied research on 2026-08-14. Citations should be verified and converted to the repository's preferred bibliography style before design approval.

## Decision

Use an immutable, validated composition image read by a small stable core, with independently built providers implementing explicitly versioned interfaces. Do not turn configuration into an executable shared library and do not expose unstable compiler-internal layouts across provider boundaries.

## Relevant prior art

### Desktop application metadata

Desktop-entry systems demonstrate that application identity, display metadata, icons, categories, actions, and associations belong in configuration rather than launcher source. Simple can import compatible metadata while compiling it into SCI instead of scanning and merging text files on runtime hot paths.

Reference: Freedesktop.org Desktop Entry Specification — <https://specifications.freedesktop.org/desktop-entry-spec/latest/>

### Compiled configuration schemas

GSettings demonstrates compiling human-readable schemas into a compact runtime form. The analogous Simple split is text SDN plus overlays at build time and one canonical indexed SCI at runtime.

Reference: GLib GSettings documentation — <https://docs.gtk.org/gio/class.Settings.html>

### Explicit component contracts

WebAssembly component-model/WIT concepts support separating interface contracts, imports, exports, and implementation composition. Simple's interface groups and SCI bindings should follow this separation without copying a foreign binary ABI wholesale.

Reference: WebAssembly Component Model — <https://component-model.bytecodealliance.org/>

### Interface querying

COM's useful principles are stable interface identity, explicit querying, and small interface surfaces instead of exposing implementation-class layout. Simple should adopt those principles while defining its own ownership and lifetime rules.

Reference: Microsoft `IUnknown::QueryInterface` documentation — <https://learn.microsoft.com/windows/win32/api/unknwn/nf-unknwn-iunknown-queryinterface(q)>

### Extensible binary structures

Vulkan's typed extension-chain model illustrates how readers can identify and skip extensions they do not understand instead of misinterpreting layouts. SCI should express required versus optional extensions explicitly and use versioned section identities.

Reference: Vulkan specification, extending structures — <https://docs.vulkan.org/spec/latest/chapters/fundamentals.html#fundamentals-validusage-pnext>

### Compiler plugin compatibility

GCC plugin version checks illustrate that plugins coupled to compiler-private interfaces require strict version matching. Simple should reserve such coupling for experimental internal pass plugins; its stable public compiler boundary should use opaque handles and versioned serialized contracts.

Reference: GCC Plugins documentation — <https://gcc.gnu.org/onlinedocs/gccint/Plugins.html>

### Incremental red/green evaluation

Rust compiler incremental compilation documents the key containment rule: recomputing a node need not invalidate downstream nodes when the relevant result remains unchanged. Simple's typed edges and compatibility digests should make that rule normative.

Reference: rustc-dev-guide red-green algorithm — <https://rustc-dev-guide.rust-lang.org/queries/incremental-compilation-in-detail.html>

### Action cache and content-addressed storage

Mature build systems separate action-key/result metadata from immutable content-addressed artifacts. Simple should follow this split and construct action keys from declared inputs only.

Reference: Bazel remote caching overview — <https://bazel.build/remote/caching>

### Diverse double compilation

DDC is a trust-verification technique for establishing source-to-binary correspondence under defined assumptions. It belongs in explicit release/security targets, not ordinary edit/build loops.

Reference: David A. Wheeler, Diverse Double-Compiling — <https://dwheeler.com/trusting-trust/>

## Synthesized domain constraints

- Configuration is inert, canonical data and must not execute code while loading.
- Runtime readers consume one pre-resolved image; text parsing, directory discovery, precedence merging, and opportunistic compilation remain outside hot paths.
- Provider ABI surfaces use fixed-width values, opaque handles, explicit buffer/allocator ownership, stable status codes, and versioned descriptors.
- Optional evolution uses descriptor prefixes or separately queried extension interfaces; incompatible ownership/layout/calling/error changes require a new major.
- Compiler boundaries begin coarse. Fine-grained plugins are introduced only where contracts are stable and performance evidence supports the boundary.
- Build propagation follows the dependency edge's relevant identity and stops when recomputation is green.
- Compatibility uncertainty fails closed for activation and conservatively rebuilds for production.
- Full bootstrap is a typed compatibility/trust event, not a directory-based heuristic.

## Research questions requiring verification

1. What exact Rust and Simple SMF layouts exist on current main, and which artifacts/readers depend on each?
2. Where is the unlanded target-graph worktree, who owns it, and can it be recovered without conflicting with active changes?
3. Which existing manifest is authoritative for each launch/provider field, and what migration preserves the “no second manifest” rule?
4. What minimum SDN parser repairs are required for deterministic overlay and sequence-of-mapping support?
5. Which host-service APIs can be exposed without violating existing runtime ownership/capability rules?
6. What current build traces establish baseline module/object/link counts, cache reuse, startup latency, request latency, and RSS?
7. Which digest implementations are semantic today and which remain placeholders?

## Recommended conclusion

The prior art supports the three-layer architecture: small stable core, compiled immutable composition image, and versioned providers. The highest-risk prerequisites are SMF wire-format convergence, authoritative manifest ownership, recoverable target-graph integration, and conservative ABI/digest semantics. The narrow first proof should remain an SCI-only application-catalog change observed through an unchanged core binary.
