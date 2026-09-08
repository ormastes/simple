# Environment-Optimized Dynamic Libraries

Status: **Focused contract and inert bridge foundations present; all executable
scenarios remain deliberately fail-fast and none is PASS evidence**.

| Scenarios | PASS evidence | Fail-fast blocked |
|---:|---:|---:|
| 32 | 0 | 32 |

## Purpose and audience

This operator-facing manual defines the verification flow for the selected
Feature A catalog-selected sibling artifacts and NFR N2 balanced production
performance. Compiler, loader, frontend, GPU, and verification owners use it
to replace each fail-fast helper with a production call and a typed oracle.
The authoritative requirements are in
`doc/02_requirements/feature/environment_optimized_dynamic_libraries.md` and
`doc/02_requirements/nfr/environment_optimized_dynamic_libraries.md`.

## Preconditions

- A qualified pure-Simple self-hosted binary. V1 contracts, the bounded catalog,
  admission/binding lifecycle, host-target planning, and inert GPU completion
  bridging exist, but production frontend and provider execution remain
  prerequisites.
- A bounded, digest-addressed catalog fixture with valid and invalid candidates,
  dependency locks, policy identities, and retained environment generations.
- Production evidence for metadata admission, mapping/callability, execution,
  completion, and retirement. Filenames, configured target flags, loaded
  symbols, or labels alone are not evidence.
- Named NFR fixtures and retained cold/warm samples, p50/p95/p99 values, RSS,
  mapped text, host/device identity, generation, and artifact digest.
- A repository-owned canonical target registry fixture and a live registry
  token for REQ-015. Its version and mapping digest must participate in every
  downstream target-profile, cache, plan, and receipt assertion.
- A production Simple opaque adapter for owned-process V3 and an admitted tool
  fixture for REQ-016. The C self-check is diagnostic evidence only; it is not
  a Simple inspection-authority integration test.

## Operator workflow

1. Inspect the sealed environment snapshot and bounded catalog.
2. Admit compatible, trusted candidates before preference ranking or native
   mapping, recording exact rejection reasons for every candidate.
3. Bind one immutable, generation-pinned dense facet plan for a new session.
4. Execute a representative batch through the typed provider contract.
5. Check the execution receipt: requested, admitted, bound, executed,
   completed, and retired are separate states.
6. Retain the receipt and measurements with the exact environment, policy,
   dependency-lock, provider-generation, and artifact identities.
7. For target-dependent artifacts, resolve the textual target through the live
   canonical registry and retain its numeric tuple, version, and mapping digest.
8. For external inspection, submit one sealed byte value to the owned V3
   process, then require exact write, stdin close, bounded dual-stream drain,
   terminal status, and reap before using its receipt.

The executable source is
`test/03_system/app/compiler/feature/environment_optimized_dynamic_libraries_spec.spl`.
Run it with the repository's pure-Simple SPipe runner after the implementation
helpers exist. Until then, every scenario deliberately fails.

## Frozen helper contract

The executable spec uses exactly these shared helper names:

- `setup_environment_catalog`: creates bounded synthetic environments and
  digest-addressed candidates.
- `step_admit_variant`: applies compatibility, trust, ABI, dependency, and
  OS/device-state predicates.
- `step_bind_provider`: publishes and pins a generation-scoped typed facet.
- `check_execution_receipt`: distinguishes requested, admitted, bound,
  executed, completed, and retired states.
- `setup_canonical_target_registry`: installs a bounded versioned canonical
  triple/alias fixture.
- `step_start_atomic_inspector`: starts one identity-owned V3 inspector with
  immutable bounded bytes and bounded output captures.
- `check_atomic_inspector_terminal`: checks exact input digest/count, complete
  close/drain/reap, terminal status, and non-authoritative failure outcomes.

Each helper currently calls `fail(...)`. This is intentional: a missing
implementation must fail closed and must not become placeholder PASS evidence.
The explicit scenario-level `fail(...)` calls remain until production oracles
replace them.

## Selected feature requirements

### REQ-001 — baseline-safe sibling selection

Inspect the bounded catalog, admit a compatible sibling, bind a new session,
and verify that the receipt distinguishes the sibling from the baseline
without an executable ISA matrix.

### REQ-002 — environment/target separation

Inspect `EnvironmentSnapshotV1`, apply exact architecture/ABI/OS/policy/vector
admission, bind the provider, and verify host environment identity is separate
from generated-code target intent.

### REQ-003 — complete variant descriptor

Load a `VariantDescriptorV1`, validate identity, placement, resource, semantic,
and dependency fields, then verify the descriptor and closure identities in the
receipt before publication.

### REQ-004 — pre-map eligibility

Present an incompatible or untrusted candidate. Verify exact rejection and
stable reason code before executable mapping or callability.

### REQ-005 — policy semantics

Exercise `prefer`, `require`, and `max`; verify that fallback is visible and
unsatisfied required requests fail without manufacturing capability.

### REQ-006 — deterministic binding plan

Publish one immutable `BindingPlanV1` with dependency lock, generations, dense
slots, selected variants, and bounded rejection reasons. Repeat with identical
inputs and compare binding identity and digest.

### REQ-007 — truthful placement lifecycle

Exercise the logical provider contract across placement adapters and retain
distinct metadata, mapping, callability, execution, completion, and retirement
states.

### REQ-008 — frontend facet boundary

Create a session through `FrontendFacetV1` without exposing AST/HIR layouts and
verify the independent legacy CPU frontend remains the reference path.

### REQ-009 — parser qualification gate

Qualify scalar parity and declared dialect coverage before any SIMD promotion;
incomplete coverage must remain non-default.

### REQ-010 — generated target evidence

Keep requested, backend-accepted, artifact-declared, emitted, selected, and
executed features as separate receipt facts; do not infer execution from a
label.

### REQ-011 — GPU placement sibling

Use the existing GPU registry adapter and require enabled-feature, program,
resource, fence, submission, completion, and retirement evidence. GPU is not a
SIMD tier.

### REQ-012 — generation cutover and drain

Cut over new sessions to a replacement generation and retain the old one until
CPU, callback, JIT, GPU, buffer, and completion pins drain.

### REQ-013 — CPU-only startup isolation

Run help, version, and reference compilation through production startup and
verify optional GPU services remain uninitialized and no missing provider is
compiled implicitly.

### REQ-014 — explainable receipts

Retain stable receipts for selection, rejection, fallback, binding, execution,
completion, quarantine, and rollback, all bound to exact environment and
artifact generations.

### REQ-015 — canonical target registry B

Resolve registered aliases through the repository-owned, versioned target
registry. Verify that aliases yield the same canonical tuple and numeric IDs;
that a registry mapping/version change invalidates target profile, cache, plan,
and receipt identity; and that unknown, ambiguous, ABI, or object-format
mismatches fail before cache or publication authority.

### REQ-016 — atomic immutable inspector input 1

Start the admitted inspector with exactly one bounded immutable byte input.
Verify its digest/count bind tool, argv, environment, process generation,
bounded output captures, stdin closure, terminal status, and reap. Empty and
maximum inputs must make concurrent progress; overflow, short write, digest
mismatch, early child exit, or unreaped state must remain non-authoritative.

## Selected NFR requirements

- **NFR-001 Safety:** zero wrong-ISA, publication-before-admission, silent
  required-fallback, and use-after-retire rows.
- **NFR-002 Selection latency:** warm p95 <= 1 ms and cold p95 <= 25 ms on the
  named reference catalog fixture.
- **NFR-003 Dispatch overhead:** generation-pinned dense dispatch <= 2% over a
  direct reference batch, with no catalog scan, lookup, allocation, spawn, or
  lifecycle lock in the hot path.
- **NFR-004 Performance:** at least one qualified parser/provider workload must
  demonstrate >= 1.15x speedup before promotion.
- **NFR-005 Memory:** selected-provider RSS increase <= 5%; unselected catalog
  infrastructure <= 2 MiB resident memory.
- **NFR-006 Coverage:** retain tiny, medium, large, Unicode-heavy, malformed,
  and vector-tail fixtures with p50/p95/p99 and identity evidence.
- **NFR-007 Capacity:** bounded catalog, dependency, rejection, queue,
  session, cache, and device capacities fail explicitly on overflow.
- **NFR-008 Determinism:** identical qualified inputs select the same variant
  and binding digest.
- **NFR-009 Startup isolation:** CPU-only cold/warm latency, mapped text, and
  uninitialized GPU state are retained.
- **NFR-010 Evidence:** unsupported host/device rows remain explicit blocked or
  unsupported rows with an owner, resume command, and retained-artifact plan.
- **NFR-011 Registry overhead:** canonical target lookup is bounded and
  allocation-free after construction, requires no network/signature service,
  and never runs in provider hot execution.
- **NFR-012 Inspector progress:** V3 atomic input and stdout/stderr drain make
  bounded concurrent progress without pipe deadlock; every input or lifecycle
  failure yields an explicit non-authoritative receipt and no leaked lease.

## Traceability

| ID | Scenario in executable spec | Oracle when implemented | Current status |
|---|---|---|
| REQ-001 | baseline-safe core and sibling artifact | selected sibling and baseline identities | FAIL-FAST |
| REQ-002 | environment facts and target intent | separated snapshot/target fields | FAIL-FAST |
| REQ-003 | complete descriptor and closure | descriptor and dependency digests | FAIL-FAST |
| REQ-004 | pre-map rejection | stable rejection phase/reason | FAIL-FAST |
| REQ-005 | prefer/require/max | visible fallback or required failure | FAIL-FAST |
| REQ-006 | deterministic binding plan | immutable plan and binding digest | FAIL-FAST |
| REQ-007 | distinct placement lifecycle | state transition receipt | FAIL-FAST |
| REQ-008 | coarse frontend facet | legacy parity and opaque boundary | FAIL-FAST |
| REQ-009 | scalar before SIMD promotion | parity and qualification evidence | FAIL-FAST |
| REQ-010 | target feature evidence | emitted/selected/executed facts | FAIL-FAST |
| REQ-011 | GPU placement sibling | submit/fence/retirement correlation | FAIL-FAST |
| REQ-012 | generation drain | pin and retirement evidence | FAIL-FAST |
| REQ-013 | CPU-only startup | no GPU initialization | FAIL-FAST |
| REQ-014 | explainable lifecycle outcomes | stable explain receipts | FAIL-FAST |
| REQ-015 | registered alias; mapping/version invalidation; invalid mapping | canonical numeric tuple; cache/plan/receipt invalidation; pre-authority rejection | FAIL-FAST |
| REQ-016 | exact input; boundary progress; terminal failures | exact input/process receipt or explicit non-authoritative outcome | FAIL-FAST |
| NFR-001 | safety matrix | zero safety violations | FAIL-FAST |
| NFR-002 | selection latency | retained cold/warm p95 | FAIL-FAST |
| NFR-003 | dense dispatch | measured overhead and hot-path audit | FAIL-FAST |
| NFR-004 | promotion speedup | qualified benchmark threshold | FAIL-FAST |
| NFR-005 | memory budget | baseline/selected RSS | FAIL-FAST |
| NFR-006 | workload matrix | complete samples and identities | FAIL-FAST |
| NFR-007 | bounded capacities | typed overflow rejection | FAIL-FAST |
| NFR-008 | deterministic selection | repeated binding digest | FAIL-FAST |
| NFR-009 | startup isolation | latency, mapped text, GPU state | FAIL-FAST |
| NFR-010 | unsupported rows | blocked/unsupported resume plan | FAIL-FAST |
| NFR-011 | `should keep canonical target lookup bounded and outside provider hot paths` | allocation-free post-construction lookup; no provider-hot-path registry access | FAIL-FAST scaffold |
| NFR-012 | `should make bounded three-pipe progress and leak no failed process lease` | no deadlock, no authority on failure, no leaked process lease | FAIL-FAST scaffold |

## Current limitation and handoff

This reconciled authored mirror is not a generated PASS manual. Do not mark the
feature, SPipe phase, verify report, or release complete from this scaffold.
The implementation lane must replace every fail-fast helper and scenario oracle
with production invocations and typed assertions, retain native evidence for
applicable host and device rows, then regenerate this manual through SPipe
docgen after production owners replace all fail-fast helpers and scenarios.
Unavailable rows stay visible as `blocked` or `unsupported`; they must never be
converted to `skip` or a green placeholder.
