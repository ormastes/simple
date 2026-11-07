# Legacy container runner safety specification

Executable source: `test/01_unit/lib/nogc_sync_mut/test_runner/container_safety_spec.spl`.
Owner: `src/lib/nogc_sync_mut/test_runner/test_runner_container.spl`.
Requirements: CTR-02 (typed arguments and ownership-scoped cleanup), RUN-01
(legacy runner integration). Audience: maintainers reviewing the orchestrator safety repair.

Status: **NOT_RUN**. No runtime, native provider, engine, elapsed-time accuracy,
coverage percentage, or release qualification is claimed. The global six-cycle
compiler repair budget was already exhausted before this lane started; no
compiler, Rust seed, test runner, or live engine is executed for this change.
Docker and Podman availability is not required by these deterministic cases.

| Case | Setup/action | Observable assertion | Requirement |
|---|---|---|---|
| Literal run arguments | Build production argv containing spaces, semicolons, dollar substitution and backticks in image, test and workspace | Full 12-element argv equals independent literal constants, including fractional CPU limit | CTR-02 |
| Literal build arguments | Build production argv with hostile Dockerfile and image strings | Full four-element argv equals independent literal constants | CTR-02 |
| Runtime whitelist | Evaluate supported, shell, injected, empty and absolute executable names | Only exact `docker` and `podman` names accepted | CTR-02 |
| Caller rejection | Call run, build, inspect and version APIs with unsupported engine | Error tuple, false or empty version without executing engine | RUN-01 |
| Operand rejection | Supply option-like images/tests, empty operands and NUL strings | Builders return errors before any process call | CTR-02 |
| Mount and network rejection | Supply colon-containing/empty source or injected network policy | Builder returns an error | CTR-02 |
| Resource/mount compatibility | Build writable bridge request, then supply zero/negative limits | Real writable argv accepted; invalid limits rejected | RUN-01 |
| Unowned cleanup | Call legacy cleanup for both supported engines and injected name | Every call explicitly returns false | CTR-02 |
| Recurrence guard | Read actual owner source | No shell helper, runtime-wide prune, or process execution in cleanup body | CTR-02 |
| Real clock owner | Read actual clock helper and run path | Monotonic owner delegation and elapsed subtraction; no zero clock stub | RUN-01 |

All cases use `step(...)` with real assertions. The source recurrence guards
supplement direct production builder and caller tests; they do not prove live
container isolation or native execution. The specs preserve the existing API
visibility; no previously private API is widened just for tests.

The legacy cleanup signature provides only an engine name, so it cannot prove
which volume belongs to this request. It returns false with no effects until a
typed exact-resource ownership API is supplied. This change adds no deletion API.

Elapsed duration remains a nonnegative millisecond tuple field. The runner samples
the existing monotonic owner; a negative starting sample fails before launch.
A failed or decreasing final sample returns an explicit nonzero error and a zero
error duration. Existing callers receive no newly introduced negative sentinel.
The legacy volume syntax cannot represent a colon in the host source; such
requests fail rather than silently changing mount fields. Literal argv prevents
shell interpretation but does not claim general container containment, image
validity, permission isolation, or live engine conformance.

When an admitted runtime becomes available, run this focused SSpec once under
its recorded exact producer identity and report actual assertion counts. Engine
conformance and elapsed-clock accuracy remain separate NOT_RUN evidence gates.
