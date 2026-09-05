# Independent Risk Assessment — scilib Fortran/CUDA Fortran Port

## Scope and Method

This memo is intentionally not a technical inventory. Other agents own ABI details, Python surface mapping, lowering mechanics, and naming audits. I reviewed the plan in `.sstack/scilib-port/state.md`, the Simple syntax quick reference, the existing naming-harmony audit in `04_naming_harmony.md`, and repo-visible language/compiler artifacts relevant to public numeric APIs and math blocks.

Two grounding points matter up front.

First, the language already exposes typed numeric literals in the quick reference: examples include `42i32`, `100u64`, `3.14f32`, and `2.718f64`. That means the language has at least one ergonomic path that does not force constructor calls for every literal.

Second, the repo explicitly lints bare primitives in public APIs. The lint text says bare primitive types in public signatures lack semantic meaning and suggests semantic unit types, newtype wrappers, or named aliases. So the “no primitive types in public API” rule is directionally aligned with current project style. What I could not verify from the visible docs is automatic coercion from a typed literal or primitive-looking literal into an arbitrary wrapper like `Float64`, `Index`, or `Shape`. The semantic diagnostics also include “type coercion from `{from}` to `{to}` is not allowed,” which suggests coercion is not something to assume. Where I discuss coercion below, I mark it as hypothesis unless directly supported.

## 1. Is “Fortran first” the right ordering?

No. The current ordering is backwards for product architecture.

The core mistake is treating BLAS/LAPACK as the foundation and ndarray as a detail. For users, ndarray is the substrate. BLAS is an accelerator and implementation backend. The public abstraction that everything else depends on is not `gemm`; it is shape, dtype, strides, slicing, broadcasting, ownership, views, and memory/device placement. Without that substrate, every early BLAS wrapper becomes a local optimum: it works for hand-fed matrices, but it does not establish the object model that NumPy-like, pandas-like, and ML-like APIs will actually use.

There is also a dependency inversion problem. If the team starts from Fortran and backend bindings, it will be tempted to let backend calling conventions leak upward: column-major assumptions, contiguous-only fast paths, opaque handle lifetimes, and solver-specific type naming. Then ndarray gets designed around what is easiest to bind instead of what is stable for Simple as a language library.

The right order for v1 is:

1. `NDArray` object model and memory model.
2. Explicit linear algebra facade that consumes `NDArray`.
3. Backend plug points behind the facade.

That does not mean “build a full pure-Simple ndarray engine first.” It means design and ship ndarray as the public contract first, even if most heavy ops immediately dispatch to BLAS/cuBLAS under the hood. If this ordering is not enforced, the project risks building a backend demo instead of a durable library surface.

My stance: make ndarray first in API design and milestone sequencing. BLAS/LAPACK should be the first performant backend for ndarray and linalg, not the first mental model for the whole effort.

## 2. Does “wide-shallow” pandas deliver value?

Mostly no. Wide-shallow pandas is one of those strategies that looks efficient on a roadmap and disappoints in real use.

Users reach for pandas for a small number of high-leverage workflows: grouping, aggregation, joins, missing-data handling, reshaping, datetime-heavy cleaning, and file IO around those operations. A “shallow” `DataFrame` that can construct columns, select columns, and print tables will satisfy demos and almost nobody else. It is especially weak if groupby is deferred, because groupby is where many real data tasks begin and end.

That said, “deep pandas” is the wrong v1 target too. Pandas is a swamp of edge cases, dtype behavior, indexing semantics, and performance traps. Trying to mimic it broadly is how this project misses its date.

So the answer is not “wide-shallow” versus “deep pandas.” The answer is: do not position v1 as pandas coverage. Position it as a narrow table library with explicit value boundaries.

The only pandas-like slice worth shipping in a 4-8 week window is:

- CSV/columnar ingestion for predictable schemas
- column selection and projection
- row filtering
- simple joins
- small aggregation set on explicit columns
- maybe one grouped aggregation path if it is intentionally narrow

Everything else should be deferred, especially pandas compatibility theater. If the team keeps the “wide-shallow pandas” story, it will create pressure to add dozens of low-depth methods that look impressive in a checklist and create permanent maintenance debt without solving a user workflow.

My stance: shallow pandas does not deliver enough value unless it includes one intentionally constrained grouped-aggregation path. Otherwise defer `std.df` to v1.1 and ship ndarray+linalg first.

## 3. CUDA Fortran v1 — moat or cliff?

It is much closer to a cliff than a moat.

CUDA Fortran is strategically attractive because it promises access to GPU-accelerated scientific libraries through a familiar numerical ecosystem. But for this project, that advantage is likely overstated and the operational downside is understated.

The main risk is toolchain dependency concentration. Requiring CUDA Fortran usually means requiring NVIDIA’s HPC SDK and `nvfortran`, with all the version coupling that implies across compiler, CUDA toolkit, driver compatibility, CI images, contributor onboarding, and user deployment. That is not just an implementation choice; it is a platform choice. Once v1 depends on that stack, the project inherits its release cadence and failure modes.

There is a second risk: backend opacity. If Simple’s first scientific backend is “Fortran calling CUDA libraries,” then debugging performance, ABI bugs, memory ownership, and device mismatch issues becomes a three-layer problem: Simple <-> Fortran <-> CUDA library. That is too much indirection for a first release unless there is a compelling capability available only through the Fortran layer.

I do not currently see that case proven. cuBLAS and cuSOLVER already have C APIs. If the v1 goal is shipping usable linear algebra on GPU, the simplest credible route is usually direct C-API FFI or a thin C shim, not adding Fortran as a mandatory middle layer. The plan says “CUDA Fortran first as backend” as if that is a simplifying move. From a project-management perspective, it is a scope amplifier.

The only reason to accept this risk is if the team is specifically trying to validate a Fortran interoperability strategy as a product pillar, not just trying to ship scientific computing support. If the actual goal is the latter, then CUDA Fortran is not a moat. It is a specialized route that narrows the contributor pool and raises integration risk.

My stance: Simple should not require `nvfortran` for v1 unless a concrete must-have capability is unavailable through the C APIs. Prefer cuBLAS/cuSOLVER via C-facing FFI and treat CUDA Fortran as an experiment or v1.1 backend. cuDF/cuML should definitely not be in v1.

## 4. Will “no primitive types in public API” make the library unusable?

Not necessarily, but it will if the team interprets the rule too literally.

The good news is that the language already supports typed numeric literals, which means a user can at least write `2.718f64` rather than constructing every scalar through a verbose object call. The repo also clearly values semantic wrappers in public APIs. So the direction is aligned with existing style.

The bad news is that semantic wrappers are not the same thing as wrapper proliferation. If every library call requires explicit construction of `Float64`, `Index`, `Axis`, `Shape`, and `Stride` objects with no literal or tuple sugar, the API will be dead on arrival. Numerical users will not tolerate boilerplate inflation on every scalar, shape, and index expression.

The biggest ambiguity is coercion. I could verify typed literals, but I could not verify that `3.14f64` implicitly becomes a public `Float64` wrapper, or that `[2, 3]` implicitly becomes `Shape`. In fact, the repo includes a diagnostic that “type coercion ... is not allowed,” which is a warning sign against assuming ergonomic conversions.

So the policy is defensible only if v1 also defines an ergonomic construction story:

- typed literals map cleanly into scalar wrapper entry points
- shapes and axes have concise literals or factory helpers
- internal kernels can still use primitives without exposing them publicly
- zero-cost or low-cost wrapper representation is documented

Without that, “no primitive types” becomes a purity tax. With that, it becomes a naming and correctness win.

My stance: keep the public no-primitive rule, but narrow it to semantically meaningful boundary types only. Do not wrap everything. `NDArray<Float64>` is useful. Requiring ritual wrappers for every temporary numeric value is not. If ergonomic literal-to-wrapper paths are not already supported, the rule must be softened for v1 or paired with explicit constructor sugar work.

## 5. Is “math-block cooperation” a disguised compiler project?

Yes. This is the most dangerous hidden scope item in the plan.

The state document describes math-block cooperation as blocks that understand ndarray, linalg, broadcasting, slicing, and expressions like `A @ B + c`, then lower them to the backend. That is not a library adapter. That is compiler surface design, lowering design, optimization policy, error-model design, and possibly type-inference work. The repo also contains a math-block runtime contract document, which confirms this area already has dedicated semantics and runtime concerns. That is useful evidence that the concept exists, but it is also evidence that the feature is its own system, not a footnote.

Project-management reality: once you promise syntax-level cooperation, every library decision becomes entangled with parser surface, block semantics, lowering hooks, shape inference, diagnostics, and fallback behavior. Delivery risk multiplies because neither the compiler team nor the library team can finish independently.

Worse, math-block cooperation is exactly the sort of feature that produces “just one more lowering tweak” churn for weeks. It can consume the entire schedule while still leaving the core scientific library half-finished.

For v1, the right move is explicit API calls, not syntax magic. If `matmul(a, b)` or `a.matmul(b)` works, users have value. If later `math { a @ b + c }` lowers to the same backend, that is a quality upgrade, not a prerequisite.

My stance: ship without math-block cooperation in v1. At most, reserve operator names or define an architecture hook contract, but do not make compiler-integrated math lowering part of the first delivery gate.

## 6. Effort estimate for v1

As currently scoped, this is not a 4-8 week project. It is roughly 10-14 engineer-months.

That range assumes:

- a stable ndarray public model
- BLAS level 1-3 coverage sufficient for credibility
- minimal LAPACK solve/decomposition subset
- wrapper/public API design under the no-primitive rule
- GPU backend integration at least for core linalg paths
- naming integration with existing `linear_algebra` and tensor surfaces
- test/spec work and debugging across interpreter/compiler paths

If math-block cooperation, pandas surface work, and scikit-learn facades remain in scope, the number moves higher fast, into the 14-18 engineer-month range. The reason is not just coding volume. It is cross-team coordination, semantic decisions, and integration debugging at language boundaries.

If leadership wants something real in 4-8 weeks, the scope must be cut to about 2-4 engineer-months of work:

- `NDArray` core object model
- explicit linalg API
- CPU BLAS or direct cuBLAS subset
- a handful of end-to-end operations that prove the shape

That is shippable. The full plan as written is not.

My stance: budget 10-14 engineer-months for the current v1 definition; budget 2-4 engineer-months for a realistic 4-8 week cut-down v1.

## 7. Recommended cuts for v1.1/v2

If the objective is to land v1 in 4-8 weeks, the team needs aggressive cuts now, not after the first slip.

Cut to v1.1 or v2:

- `std.df` as a pandas-analogue surface, except maybe CSV ingestion helpers that feed ndarray or a minimal table type
- all scikit-learn-style API surface
- cuDF and cuML bindings
- CUDA Fortran as a required toolchain path
- math-block cooperation as a delivery requirement
- broad LAPACK coverage beyond a tiny solve/decomposition subset
- backend-swappability promises beyond basic interface boundaries
- “wide-shallow” method-count expansion for compatibility optics

Keep for v1:

- `NDArray<T>` core with shape, dtype, indexing, slicing, reshape, and broadcasting rules
- explicit linalg facade over ndarray
- a minimal backend: either CPU BLAS/LAPACK first, or direct cuBLAS/cuSOLVER subset if GPU is non-negotiable
- semantically meaningful public wrapper types where they add clarity
- a short list of end-to-end proofs: vector ops, matmul, solve, broadcasted elementwise ops

This cut is not conservative. It is the minimum needed to avoid a fake v1 that is broad in namespaces and shallow in user value.

The naming audit already shows existing `linear_algebra`, tensor, and ML surface area in the repo. That means every extra namespace promise has migration and collision cost. The right response is not to harmonize everything in one release. The right response is to ship one strong vertical slice and let naming convergence follow evidence.

Single biggest risk: math-block cooperation and CUDA Fortran-first backend strategy combine to turn a library port into a compiler-plus-toolchain project.
Proposed v1 scope cut: ship `NDArray` + explicit linalg + minimal BLAS/LAPACK or direct cuBLAS/cuSOLVER subset; defer pandas, sklearn, cuDF/cuML, and math-block lowering.
