<!-- codex-research -->
# Item 5: kernel/extension aspect loading and binary size

Date: 2026-10-02. Research baseline: `e10963a3b065dde1643c777512c3988526973957`.
Scope: item 5 of `doc/03_plan/seven_plans_host_completion_2026-09-29.md`.
This additive document preserves prior research and selected requirements.

## Retained contract

The selected 2026-09-02 requirements in
`doc/02_requirements/feature/runtime_optional_provider_binary_size_optimization.md`
remain authoritative: REQ-001 through REQ-015 and NFR-001 through NFR-007.
Registration is metadata only; first demand admits ABI, target, architecture,
digest, dependency, and policy before activation. Stable pure-Simple providers
are preferred; effectful dual mode executes once. Every demanded language
feature and supported architecture must remain available. Sealed compiled
artifacts replace source parsing on demand. Debug and ordinary release retain
diagnostics; release-small requires closure proof before excluding unwind/RTTI.

The complete endpoint includes exact kernel dependency exclusion, in-process
extensions, packaging, failures, lifetime, matched size, startup, and RSS.
Command capsules and SQLite probes are prerequisites, not substitutes for
full extension scope or cross-target evidence. Kernel/driver design remains
MDSOC-only; do not introduce MDSOC+/ECS by default.

## Current source observations

| Source | Observed behavior | Remaining evidence or implementation |
|---|---|---|
| `src/compiler/99.loader/provider_admission/state.spl` and `admission.spl` | Atomic metadata admission, package/ABI/dependency checks, cached rejection, effect-owner receipt | Descriptor has no explicit target/architecture/policy contract; no proof of actual load/init or production dispatch |
| `src/compiler/99.loader/provider_call_boundary_v1.spl` | Validates provider identity, ABI digest, symbol and effect owner; yields dispatch permit | Module explicitly performs no dispatch; loading and payload execution remain open |
| `src/os/smf/provider_loader.spl` | Actual dynamic-library open, callable query validation, typed rejection, pin/session ownership, CLI invoke and checked close | Reuse this owner; integrate immutable installed manifest and demand activation rather than inventing another loader |
| `src/runtime/runtime_sqlite_demand.c` | Linux first-use SQLite bridge exists | Does not establish general provider closure, all target support, installed manifests or size cohorts |
| `src/app/cli/_CliMain/main_and_help.spl` | Lines 45-46 directly import UI/Office; lines 312-317, 610-612, 670 call them; line 627 uses source `cli_run_file` for provider command | Metadata-only command advertisement and cached admitted artifact execution remain required |
| `src/compiler/70.backend/linker/runtime_feature_closure.spl` | Named historical implementation is absent in this baseline | Existing retained-symbol/archive selection is not an exact RuntimeFeatureClosureV1 proof |

Historical reports in the 2026-09-02 optional-provider plan include successful
isolated Linux SQLite admission and 13,544-byte matched hello diagnostics.
They must not be relabeled as current-host, admitted release-small, complete
CLI, provider-closure, or cross-platform evidence.

## Existing specifications and their limits

- `test/03_system/app/native_build/feature/executable_size_reduction_spec.spl`
  mostly reads Rust-source tokens. Missing audit products are replaced by
  assertions against requirements text. Its PASS cannot certify runtime behavior.
- `test/05_perf/compiler/runtime_optional_provider_binary_size_spec.spl`
  explicitly uses synthetic Stage4/startup evidence; it proves BS7 checker
  mutation rejection, not production startup admission.
- `test/01_unit/compiler/loader/provider_admission/provider_admission_spec.spl`
  exercises atomic terminal states with intentionally invalid archive fixtures.
  Preserve that useful state coverage without treating it as artifact activation.
- `test/02_integration/app/ui_access_sqlite_demand_rejection_spec.spl` and
  `ui_access_sqlite_demand_concurrent_spec.spl` provide focused real bridge seams.
- `test/01_unit/compiler/99.loader/provider_call_boundary_v1_spec.spl`
  covers a permit boundary, not execution.

## Concrete modern SSpec acceptance inventory

| Acceptance | Required authoritative oracle |
|---|---|
| Register unused provider | Actual load/map/init counters remain zero; no source parse, decompression or provider scan |
| First demand and repeated/concurrent use | Correct payload result; exactly one identity admitted and initialization performed; waiting callers share verdict |
| Admission rejection | Independently mutate missing artifact, digest, ABI, target, architecture, capability, dependency and callable symbol; typed refusal and zero effects |
| Stable pure-Simple selection and rollback | Actual provider identity, result/error parity, retained receipt and successful previous artifact restoration |
| Effectful dual mode | Observable effect count is one; pure bounded shadow comparison separately tested |
| Exact NoGC kernel closure | Inspect real sections, symbols, archive members, constructors, exports and dynamic dependencies; all retained roots have reasons; forbidden collector/compiler/backend/provider roots absent |
| Enabled extension | Actual feature works; only declared provider dependencies appear; required foreign unwind/RTTI lives in provider artifact |
| Lifetime | Live pins refuse close, released pins allow owned close, stale handles cannot dispatch; do not assume native close means immediate unmapping |
| Packaging and CLI | Atomic immutable manifest installation, help without activation, admitted compiled artifacts, exact stdio/exit parity, no raw-source fallback |
| Artifact evidence | Link map, removed-section log, section sizes, ranked symbol sizes, dependencies, stripped/unstripped hashes bind compiler/source/target/profile |
| Size and resources | Below 2 MiB unstripped per native target; Linux release-small <=15,360 bytes and <=1.05x matched C; admitted non-ELF format allowance; startup/RSS <=1.10x same-host Python |
| Cohorts and targets | >=30 development or >=100 release samples, p50/p95/RSS and identities; separate each supported target, unavailable targets never PASS |

## TDD interfaces and lane ordering

Proposed helper contracts require parent naming review before implementation:
`item5_build_fixture_v1` produces real artifacts and hash-bound build receipt;
`item5_observe_process_v1` captures exit/stdout/stderr and activation observations;
`item5_inspect_link_v1` returns actual retained roots/sections/dependencies;
`item5_mutate_provider_v1` produces an independently altered immutable artifact;
`item5_check_evidence_v1` yields a typed evidence verdict. Missing implementations
must fail explicitly, never fabricate passing receipts.

Manual steps: "Build the admitted kernel and sealed extension artifacts";
"Observe registration before any capability demand"; "Demand the selected
capability once"; "Inspect retained roots and dynamic dependencies"; "Reject
the mutated provider before any effect"; "Release provider pins before closing
the session"; "Compare matched size and startup cohorts".

Bounded first lane: immutable manifest/target policy around existing loader,
red missing/digest/ABI/target/capability tests, implementation, one green run.
Parallel separate-worktree lanes may cover exact closure and modern runtime
fixtures. Full CLI cutover, packaging, all providers/targets, and cohort gates
remain required; completing the first lane cannot mark item 5 done.

## Host discovery

Ubuntu WSL bounded discovery on 2026-10-02 inspected `/home` and `/opt` only:
`/home` is empty; no `simple` executable was found within depth 4 under `/home`
or depth 3 under `/opt`. No admitted WSL runtime identity/provenance was found.
This is a bounded discovery result, not evidence that the host has no runtime.
