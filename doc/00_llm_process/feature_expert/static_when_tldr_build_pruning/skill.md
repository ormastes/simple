# Static conditions, symbolic TLDR and build pruning

The selected user proposal is
`doc/01_research/local/simple_static_when_tldr_build_pruning_plan.md`.
Preserve the proposal verbatim; record implementation gaps separately.

Use the compiler_language feature group plus the longest applicable source-layer
route. The compiler owns typed static-domain identities, Boolable phase checking,
guard extraction, conditional source regions, symbolic public summaries and
dependency closure. Build/test runners consume this compiler contract; they must
not define different condition semantics or supply missing correctness authority.

Unknown domains/members are diagnostics, never false. Inactive branches must not
resolve imports, but structural scanning must validate delimiters and directives.
Runtime Boolable conversion does not authorize arbitrary evaluation before import
resolution. Never prune an edge whose guard/dependency/effect coverage is unknown.

Portable summaries preserve symbolic guards across targets. Target/config/domain
universe, compiler/schema versions, dependencies, aspects and captured state bind
the appropriate cache layers. Timestamps alone are not content authority. A TLDR
interface result is not a final object/link result.

Measure standalone and runner-mediated builds on identical inputs. Require
correctness, memory and performance evidence, negative controls and CPU/GPU parity
before enabling optimized paths. A plan, model proof or diagnostic seed result
does not establish native/bootstrap qualification.
