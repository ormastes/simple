<!-- codex-design -->

# Feature Requirements: Minimal-Bootstrap Configuration-Composed Dynamic Architecture

## Status

Selected. The user's executive decision selects a small static core, one immutable Simple Composition Image, and independently built versioned providers. There is no pending options file for this feature.

## Goal

Normal feature development rebuilds the smallest named target, provider, or composition projection justified by an explicit dependency. Full bootstrap remains an explicit incompatibility, convergence, or trust operation.

## Requirements

### REQ-001 — Canonical composition image

The system shall compile deterministic SDN composition source into one immutable `SimpleCompositionImageV1` (`.sci`, magic `SCI\0`) whose canonical ordering makes semantically equivalent reordered source byte-identical.

### REQ-002 — Fail-closed image reader

The reader shall reject unsupported required sections, malformed bounds, overlapping sections, content-digest mismatches, duplicate bindings, undeclared runtime slots, unsafe artifact paths, and unresolved required interfaces. Unknown optional extension sections shall be skipped.

### REQ-003 — One manifest ownership

SCI shall be the configuration source and shall project launch/security fields into the existing `SimpleArtifactManifest`; it shall not introduce an independently authoritative launch manifest. Launcher registrations, desktop app metadata, associations, shortcuts, and packaged aliases shall migrate toward this projection.

### REQ-004 — Stable core boundary

`simple-core` shall read SCI, validate policy and artifacts, query/load providers, expose basic diagnostics/recovery commands, and delegate ordinary commands without statically importing the full compiler driver or product command implementations.

### REQ-005 — Provider discovery contract

Every dynamic provider slice shall expose `SimpleProviderQueryV1`. Requests identify interface, version, host ABI, target, and requested capabilities; results identify status, provided version, descriptor prefix, provider context/identity, and implementation/ABI digests.

### REQ-006 — ABI-safe interfaces

Provider contracts shall use fixed-width scalars, explicit views/buffers, opaque handles, host-supplied allocation, versioned POD descriptors, and stable status codes. They shall not expose `any`, native Simple object/text/container layout, mutable AST/HIR/MIR, unwinding, or ambiguous ownership.

### REQ-007 — CLI provider slice

The root command registry shall resolve command summary metadata from SCI and dispatch a leaf command through `SimpleCliCommandV1`. A private leaf-provider change shall rebuild only that provider and, when its exact digest is locked, the SCI projection—not `simple-core` or the compiler provider.

### REQ-008 — Application provider slice

The launcher shall obtain an application record from SCI and launch it through `SimpleAppLaunchV1`. Changing display metadata, shortcut, or association shall rebuild only SCI and shall be observable through an unchanged core executable.

### REQ-009 — Explicit build/config separation

Provider build actions and SCI compilation shall remain distinct named targets. Runtime activation shall never compile missing source or construct shell compilation commands; it shall return a typed missing/incompatible-provider diagnostic.

### REQ-010 — Compatibility-driven graph

The build graph shall use typed edges and the relevant implementation, compile-interface, ABI, compile-semantic, tool-behavior, runtime-contract, link-export, and configuration-projection identities. Re-evaluation shall stop propagation when the edge-relevant identity is unchanged.

### REQ-011 — Explainable rebuild decision

Build-explain evidence shall report requested target, changed interface groups, relevant digest deltas, selected rebuild closure, cache reused/rebuilt counts, `bootstrap_required`, and typed `bootstrap_reason`. `Unknown` compatibility shall rebuild conservatively and shall never authorize reuse.

### REQ-012 — Typed bootstrap reasons

Full bootstrap shall require a non-empty typed reason: admitted producer incompatibility with required language/runtime/artifact/core contract, missing/corrupt/unsupported seed, explicit self-host convergence, release trust verification, or DDC. Paths, cache misses, app/CLI registration, docs, tests, and provider-private edits are not sufficient reasons.

### REQ-013 — Explicit trust targets

Self-host convergence and diverse double compilation shall remain explicit named release/trust targets and shall not enter ordinary feature target closures.

### REQ-014 — Conservative provider evolution

Interface identity shall include ID, major, minor, descriptor size, and ABI digest. Known compatible prefixes or queried optional extension interfaces may evolve within policy; incompatible ownership, layout, calling, required-operation, or error changes require a new major. Duplicate IDs, short required descriptors, unstable query results, and unsupported majors shall fail closed.

### REQ-015 — Generation-safe activation

Provider activation shall verify exact artifact identity, capability ceiling, allowed path, and process-callable code; activation shall be atomic and an in-use provider generation shall remain pinned until its handles are released.

### REQ-016 — Coarse compiler boundary

The first compiler provider shall use opaque sessions and request/result handles rather than splitting or exporting lexer, parser, AST, HIR, or MIR internals. `CompilerDriverV1` shall be the later boundary used to remove the concrete compiler-driver import from the minimal core.

### REQ-017 — No destructive cache invalidation

Action results and immutable artifacts shall be keyed by declared inputs and content identities. Format changes shall select a new namespace; feature builds shall not globally clear caches.

### REQ-018 — Development workflow guidance

SPipe, skill, LLM-process/wiki, and developer guidance shall direct agents to focused tests, the smallest named target/provider/SCI projection, compatibility evidence, and only then the smallest incompatible bootstrap stage. Every relevant guidance surface shall be updated or explicitly marked `N/A` with reason.

## Exclusions

- The first slice does not split lexer, parser, HIR, or MIR into dynamic providers.
- Cross-platform native/SMF parity is not claimed without platform evidence.
- This feature does not authorize release, tagging, version bumping, or pushing.
