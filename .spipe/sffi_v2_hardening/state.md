# Feature: SFFI v2 Hardening

## Raw Request

`$sp_dev harden sffi robust with the research, design and plan doc. update the doc and go pherallel. and sync gh and push. also harden existing sffi of impl. with pherallel agents`

## Task Type

bug

## Refined Goal

Make existing Simple foreign-function execution fail closed and ABI-contract-driven across interpreter, JIT/native registration, dynamic loading, and documented safe wrappers, with no missing return, unresolved symbol, unsupported conversion, null pointer, or bridge failure able to fabricate a usable `nil`, zero, false, empty value, or passing test result.

## Acceptance Criteria

- AC-1: Claim or create tracked bug records for non-optional fallthrough fabrication and generic dynamic-SFFI ABI fabrication before source edits; each record names the exact owner paths, baseline symptom, assignee, and pure-Simple-first boundary rationale.
- AC-2: Reproduce before fixing: a non-unit Simple function that falls through is observed producing or accepting `nil`, and the generic dynamic bridge is shown accepting at least one unsupported value or null function address as zero/default; retain commands and exact diagnostics.
- AC-3: Inspect the self-hosted compiler/runtime owner first. Rust-seed edits are permitted only where evidence shows the current production behavior is below or mirrored across that boundary; the bug record documents why the Rust lane is necessary and how parity will be maintained.
- AC-4: Freeze shared interfaces `SffiFunctionContractV2`, `SffiReturnOrigin`, `SffiReturnContract`, `SffiErrorCode`, `SffiTypedThunk`, and `SffiProviderRegistryV2`; reserve `E-SFFI-001..020`; no parallel lane creates a private competing definition.
- AC-5: Missing body results are classified before value construction: unit fallthrough yields unit, explicit optional absence yields `Option.None`, and non-optional or hardened accidental-optional fallthrough yields the stable missing-return diagnostic rather than `Value::Nil`.
- AC-6: Replace the unit-only terminal validator in the affected execution path with a total return-contract validator covering explicit return, tail value, unit fallthrough, optional absence, foreign raw result, and missing return.
- AC-7: Existing dynamic SFFI conversion becomes fail-closed: unsupported arguments, embedded NUL text, arity overflow, null function pointers, unknown symbols, and unsupported signatures return typed errors; no path maps them to integer zero or leaks temporary C strings.
- AC-8: The generic all-`i64` transmute dispatcher is unavailable in robust/critical execution. Supported scalar signatures use typed thunks or an explicitly unsafe legacy/development path that cannot publish high-level safe values or run in critical mode.
- AC-9: Raw extern calls retain or gain lexical `UnsafeCapability.Ffi` enforcement in every changed compiler lane; generated safe wrappers validate status/null/sentinel/descriptor and ownership contracts before lifting to `T`, `Option<T>`, or `Result<T, SffiError>`.
- AC-10: Native/JIT/dynload registration rejects missing symbols and null pointers before activation and uses one compiler-owned registry/contract identity for changed paths; weak fabricated production providers are removed or made explicit optional capabilities.
- AC-11: Exact regression coverage proves the original missing-return and unsupported-conversion cases. Adjacent coverage includes explicit unit fallthrough, explicit optional `nil`, missing symbol, null function pointer, embedded-NUL text, and a supported typed scalar call. Each spec uses real assertions and canonical `step("...")` flows; placeholders use `fail("TODO: implement SFFI v2 oracle")`, never pass stubs.
- AC-12: Sabotage evidence records green -> deliberately re-broken red -> restored green for both the return validator and dynamic dispatch error path; non-biting sabotage is disclosed and broadened.
- AC-13: Cross-lane evidence distinguishes interpreter, default run/JIT, native/AOT, sealed dynload, and SimpleOS availability. Unavailable lanes remain explicit blocked/TODO rows with owner, prerequisite, exact resume command, retained artifacts, and reviewer; they are never skipped or counted as PASS.
- AC-14: Performance inspection proves supported typed scalar/opaque-handle hot paths perform no per-call hashing, signature verification, symbol-name lookup, mutex-map lookup, generic descriptor decoding, or temporary heap leak; status/null checks remain enabled by default.
- AC-15: Update repository knowledge in the same change: research under `doc/01_research/`, requirements or explicit selected-decision record under `doc/02_requirements/`, architecture under `doc/04_architecture/`, detailed design under `doc/05_design/`, implementation/agent/system-test plans under `doc/03_plan/`, generated/manual spec docs under `doc/06_spec/`, the canonical `doc/07_guide/platform/ffi/sffi.md`, SFFI feature/layer expert pages under `doc/00_llm_process/`, and every unfixed gap under `doc/08_tracking/bug/`. Process-skill/agent/command files are `N/A` unless SPipe workflow itself changes; if it does, update all required process mirrors before verify.
- AC-16: SFFI SSpec/manual artifacts have no placeholders, use built-in matchers, trace requirement IDs, produce an operator-readable mirrored manual with `0 stubs`, and keep `find doc/06_spec -name '*_spec.spl' | wc -l` equal to `0`.
- AC-17: Focused Rust and Simple tests, changed-file lint, duplication, direct-env/runtime guards (`--working` and `--staged`), applicable compiler/lib/MCP checks, and no-conflict/tree/rules push gates pass once against stable binary/source identities; at most three distinct fix/verify cycles are allowed.
- AC-18: The implementation, docs, specs, and verification evidence are committed from the isolated SFFI worktree, linearly rebased/landed onto the main worktree without absorbing unrelated dirty files, synchronized with `origin/main`, and pushed to GitHub without bypassing repository hooks.

## Scope Exclusions

- Full cryptographic evidence-manifest/signature admission (P4+) is designed and planned but is not silently claimed complete by the immediate P0/P1 implementation.
- Wholesale migration of every existing provider is outside the first implementation slice; every remaining unsafe provider stays inventoried and planned.
- Formal proof receipts for third-party C/C++/Rust implementations remain separate provider work unless an existing provider in the changed scope already has a proof harness.

## Cooperative Review

- Parallel implementation lanes:
  - `return_contract`: seed/self-hosted return-origin and total validator ownership.
  - `dynamic_dispatch`: dynamic SFFI conversion, null/symbol failure, scoped temporary storage, typed scalar dispatch.
  - `registry_safety`: compiler-owned contract/unsafe/registration inventory and minimal implementation slice.
  - `specs_docs`: reproduce-first SSpec/probes, manual, architecture/design/guide/expert docs.
  - `verification_review`: independent integration review, sabotage matrix, and focused gate audit.
- Merge owner: `/root`.
- Final normal/highest-capability reviewer: `/root` after independent `verification_review` findings.
- Shared interface names: `SffiFunctionContractV2`, `SffiReturnOrigin`, `SffiReturnContract`, `SffiErrorCode`, `SffiTypedThunk`, `SffiProviderRegistryV2`.
- Manual flow helpers: `step("Reject a missing non-optional return")`, `step("Reject an unsupported foreign argument")`, `step("Reject a missing or null symbol")`, `step("Admit and invoke a supported typed scalar thunk")`.
- Setup/checker helpers: `sffi_missing_return_fixture`, `sffi_dynamic_fixture_provider`, `validate_sffi_return_contract`, `expect_sffi_error_code`, `check_sffi_cross_lane_matrix`.
- Fail-fast placeholder rule: `fail("TODO: implement SFFI v2 oracle")`; no `pass_todo`, empty body, or tautology.
- Generated-manual review owner: `specs_docs`, with final review by `/root`.

## Runtime Boundary Decision

- `runtime_need`: existing defect is inside interpreter/foreign ABI dispatch, so runtime-adjacent work is required.
- `facade_checked`: safe Simple facades cannot repair a fabricated value after the ABI bridge has erased its origin.
- `chosen_path`: fix the compiler/interpreter owner and generate validated safe wrappers; avoid adding app/spec-local raw extern aliases.
- `rejected_shortcuts`: wrapper-only null check, unsupported-value-to-zero compatibility, weak fabricated provider, unchecked `NonNull`, binary-symbol grep, source-text-only spec, and Rust-seed-only semantics.

## Phase

implementation-review

## Log

- dev: Created state file with 18 acceptance criteria (type: bug); froze shared interfaces and five parallel lanes.
- return_contract P0: pure-Simple MIR lowering now records fatal `E-SFFI-016` before a non-unit operand-less return can publish; the Rust interpreter mirrors it by classifying `SffiReturnOrigin` before value construction and preserving unit fallthrough plus explicit optional `nil`.
- native bridge review: null `dlclose` now returns its documented failure status; generic value-returning i64/f64 bridges remain blocked on a coordinated status/out ABI because their current zero fallback is indistinguishable from a valid result. The gap is tracked in the dynamic-SFFI bug record and is not counted as PASS.
