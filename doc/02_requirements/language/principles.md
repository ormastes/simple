# Simple language principles

Status: selected language direction, 2026-10-06. The static-condition decisions
below are requirements for the next implementation, not a claim that existing
seed or self-hosted compilers already implement them. Existing behavior remains
versioned until migration and interpreter/native parity checks pass.

Source decision: [user-supplied static-condition and pruning plan](../../01_research/local/simple_static_when_tldr_build_pruning_plan.md).
Implementation requirements: [static condition and TLDR pruning](../feature/static_when_tldr_build_pruning.md).
Architecture: [guarded build closure](../../04_architecture/static_when_tldr_build_pruning.md).

## Typed identities for semantic domains

Closed and explicitly extensible semantic domains use typed identities. OS,
architecture, ABI, backend, mode, profile, features and capabilities must not
derive their identity from unchecked text comparisons. External configuration
text is decoded and validated at the boundary.

The selected spelling `os.windows` denotes a typed member-selection predicate.
It is not an arbitrary enum value made truthy and is not a string comparison.
One-of domains select one member; set domains test membership. Extensions have
stable, namespaced identities and collision checks. The frozen domain universe
is available before dependency discovery; a module import cannot mutate it.
Unknown domains and members are errors, including in structurally scanned
inactive branches. They never silently evaluate to false.

## One condition concept, explicit evaluation phases

`if`, `while`, match guards and `@when` share the Boolable condition concept.
Runtime condition conversion and dependency-scan evaluation have different
phase permissions. Arbitrary enum values have no implicit truth conversion in
the selected policy; any conversion must have explicit typed semantics.

Dependency-affecting `@when` accepts only the bounded, statically decidable
subset: Boolean literals, typed static-domain predicates, approved pure static
predicates, `not`, `and`, `or`, and parentheses. General CTFE, filesystem probes,
environment reads, runtime state and unresolved imported functions cannot decide
which dependencies exist. A user-defined Boolable conversion does not bypass
this restriction.

Use the existing `@when` / `@elif` / `@else` / `@end` structural family; do not
introduce a second unrelated static-if grammar. Ordinary `if` remains a runtime
construct. Extract a static dependency guard from it only when phase analysis
proves the condition static and dependency/effect coverage is complete.
The proof must resolve the predicate's identity: a runtime variable named `os`
does not become a static domain because its field access has the same spelling.

## Prune before resolving, preserve structural diagnostics

A proven-false branch must not cause filesystem dependency probes, import/name
resolution, ordinary AST construction, type checking or code generation for its
inactive body. A cheap structural scan still validates directive nesting,
condition syntax and lexical boundaries. Unterminated strings/comments or
directives cannot be concealed by making a condition false.

Unknown condition classification is not false. Diagnose an invalid structural
condition, or retain conservative dependency coverage for legacy summaries that
cannot prove completeness. Never silently omit an unresolved dependency.

## Symbolic interfaces and complete semantic roots

Portable TLDR summaries retain symbolic guards and stable typed references.
Target selection evaluates those guards for a build; it must not erase other
targets from the reusable summary. Generate TLDR imports from guarded semantic
references, not by copying the source import list or reparsing each symbol.

Pruning preserves module initializers, exports/re-exports, macros and CTFE,
generated declarations, trait/coherence and extension contributions, AOP
selectors/advice, runtime/linker/provider registration, FFI/link metadata,
declared reflection and test registration. Unknown effect coverage retains the
module. Side-effect-only dependencies need explicit representation; no new
side-effect-import syntax is selected by this document.

## Shared compiler semantics and cache authority

The standalone compiler owns condition evaluation, summary validation and build
closure. The build runner, test runner, interpreter, native backends and optional
GPU/SIMD frontend consume the same versioned contract. Runner availability must
not change what a source file means or make standalone compilation incomplete.

Cache identity includes the relevant source/dependency witnesses, grammar and
summary versions, domain universe, target/configuration projection, and producer
identity. Aspect cut targets, captures and semantic effect changes invalidate
affected artifacts. Host file observations remain separate from portable content
identity; equal modification time and size alone cannot authorize reuse.

A validated TLDR can unblock interface-dependent work. Link readiness requires
validated final OBJ/SMF artifacts and complete dependency/effect closure. Missing
or incomplete legacy summary coverage falls back to source work; it is not a hit.

## Predictable cost and evidence before activation

No-condition files use a no-allocation fast path. Conditional scanning is one
bounded pass; guards are interned and shared rather than copied per declaration.
Summary construction and closure traversal scale with relevant entries, edges
and unique guards. Do not make a SAT/BDD solver a production dependency.

Optimization evidence must show work performed and work avoided, output parity,
cache invalidation correctness, CPU/GPU agreement, latency and peak memory.
Compare standalone and runner builds on identical staged sources and compiler
arguments, with separate cold and warm results. Failed builds do not count as
speedups. A formal policy model is useful evidence but does not replace native
concurrency, memory or compiler correctness tests.

## Migration is observable

The current truthiness implementation includes implicit enum truthiness, so the
selected Boolable rule is a language behavior change. Introduce an explicit
language/condition-policy version, migration diagnostics and parity tests before
switching defaults. Keep legacy `@cfg` compatibility during the documented
migration; removal requires a separate release decision. Documentation must
distinguish selected design, implemented capability and qualified default.
