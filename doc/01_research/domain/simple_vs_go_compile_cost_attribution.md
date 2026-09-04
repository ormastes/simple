# Simple versus Go compile-cost attribution — domain research

Date: 2026-09-02

## Method

Only primary Go project documentation and source are used. These sources explain
why Go is a demanding baseline; they do not supply a matched timing result for
this repository.

## Go's relevant cost model

1. **Package action graph and parallelism.** Go's `Builder` deliberately holds
   no per-package state because packages build in parallel. Build actions have
   explicit dependencies and inverse triggers. This bounds scheduling to the
   package action graph rather than compiling a repository as one unit.
   Source: [Go action graph source](https://github.com/golang/go/blob/master/src/cmd/go/internal/work/action.go).
2. **Content-derived build caching.** The go command uses action IDs to reuse
   cached package outputs, accounts for source/compiler/options changes, stores
   cache data in a host-level cache safe for concurrent invocations, and
   periodically trims old entries. Sources:
   [go command cache documentation](https://pkg.go.dev/cmd/go#hdr-Build_and_test_caching),
   [Go cache/build-ID implementation](https://github.com/golang/go/blob/master/src/cmd/go/internal/work/buildid.go), and
   [Go build execution source](https://github.com/golang/go/blob/master/src/cmd/go/internal/work/exec.go).
3. **Export data avoids dependency source compilation.** Go package artifacts
   carry export data consumed by importers. Unified IR participates in package
   import/export and inlining, so downstream compilation does not require
   recursively reparsing every dependency source file. Sources:
   [Go compiler README](https://github.com/golang/go/blob/master/src/cmd/compile/README.md) and
   [Compiling a package](https://go.dev/talks/2017/exporting-go.pdf).
4. **Bounded compiler pipeline.** Go parses/type-checks package files, constructs
   IR, performs middle-end optimization, lowers through walk, then generates and
   optimizes SSA. This is substantial work, but normally only for cache-missed
   packages on the action graph. Source:
   [Go compiler README](https://github.com/golang/go/blob/master/src/cmd/compile/README.md).
5. **Generic sharing.** Go's implementation combines GC-shape stenciling with
   dictionaries rather than creating a distinct body for every concrete type
   invocation. This can reduce generated-code and compile-work multiplication
   relative to pure monomorphization. Source:
   [Go generics implementation design](https://github.com/golang/proposal/blob/master/design/generics-implementation-dictionaries-go1.18.md).
6. **Optimization budget is deliberate.** The Go project explicitly notes that
   more aggressive optimization can increase build time, and its production
   compiler balances runtime gains against compilation cost. Sources:
   [Go PGO article](https://go.dev/blog/pgo) and
   [Go 1.21 release article](https://go.dev/blog/go1.21).

## Phase-by-phase comparison hypotheses

| Phase | Go advantage likely relevant to Simple | Status |
|---|---|---|
| Source discovery/VFS | Package loader enumerates package inputs; cached actions avoid compiler work. Simple still has recursive discovery routes. | Hypothesis; measure cumulative directory time. |
| Parsing | Go parses only cache-missed packages. Simple's package-level early cutoff is not production-proven. | Strong hypothesis. |
| Semantic/HIR | Go imports serialized package information. Simple retains large HIR/validation structures in Stage3 evidence. | Strong local evidence plus architectural comparison. |
| Reverse references | Go's explicit import/action graph directly constrains dependents. Simple's richer typed reverse projections add validation cost but should enable precise invalidation. | Hypothesis until native work-set receipts exist. |
| Generics | Go shares bodies by GC shape and dictionaries. Simple's specialization model may generate more concrete bodies. | High-ranked hypothesis; count bodies and bytes. |
| MIR/SSA | Both perform lower-level optimization. Simple may send a larger admitted closure through MIR before cache reuse. | High-ranked hypothesis. |
| LLVM/Cranelift codegen | Standard Go uses its integrated SSA backend; Simple's LLVM release path can carry a larger optimization/tool startup cost, while Cranelift is the fair fast-development comparison. | Strong architectural hypothesis. |
| Runtime/stubs | Go packages/runtime are ordinarily cached archives. Simple bootstrap/native flows may regenerate provider bundles and stubs. | Moderate hypothesis. |
| Linking | Go links only after package action resolution and can bypass some work through cache decisions. Simple M4 explicitly validates relink behavior. | Measure separately. |
| Cache publication | Both hash and publish. Go's mature host-shared concurrent cache is the baseline; Simple's shared root was just introduced and remains unqualified. | Additive unless I/O pressure is high. |
| SCV snapshot | No direct Go equivalent in ordinary builds; this is extra Simple work required for immutable provenance. It should be inventory-based and bounded. | Additional Simple-only cost, probably small if designed correctly. |
| Qualification | Simple's bootstrap qualification is stronger than ordinary `go build`; it must not be included in a user compile comparison. | Methodological distinction. |

## Ranked conclusion

The most likely explanation for a persistent Simple/Go gap is not one extra
virtual-file abstraction. It is the multiplication of work after discovery:
coarse or incomplete package reuse, semantic/HIR retention, concrete generic
specialization, MIR processing, and LLVM code generation. VFS and SCV are
additional fixed costs and can become visible on warm no-op builds, but they
cannot plausibly explain multi-minute clean builds unless instrumentation proves
they are repeatedly invoked per package or request.

The correct target is therefore not merely "make VFS faster." It is: admit the
exact package/SCC closure; consume compact exported metadata; share or cache
generic work; choose Cranelift for fast development codegen; reserve LLVM's
larger optimization budget for release builds; and keep snapshot, hashing, and
publication bounded and host-shared.

## Matched benchmark requirements

- Equal source bytes, AST-node count, package count/depth/fan-out, generic
  instantiation count, target, optimization intent, debug/strip policy, and
  runtime-linkage semantics.
- Separate clean, warm no-op, private edit, public edit, and foundational edit.
- Report compiler-core and qualification totals independently.
- Report wall median/p95, CPU, max RSS, I/O, package/SCC work set, generated
  function count, IR bytes, object/archive bytes, and link time.
- Do not claim a 2x ratio until both tools complete the same corpus on the same
  host and the confidence interval excludes larger ratios.

