# Report 2 — Header/preprocessor cache engine and resource sharing

**Date:** 2026-09-25  
**Status:** Proposed implementation and correctness contract.  
**Companion:** [Variation policy](01_macro_header_policy.md); [integration](03_clang_cmake_ninja_integration.md); [qualification](04_ci_tests_implementation.md).

## 1. Reuse several layers; do not invent one universal header cache

| Layer | Reusable representation | Necessary boundary |
|---|---|---|
| Raw input | Immutable source/file bytes | Content digest; consuming action keeps path semantics. |
| Lexical resource | Provider-native lexical/index data | Language/encoding/lexical options and format identity. |
| Preprocessing result | Tokens plus source mapping and all relevant state effects | Complete entering state and supported replay. |
| Prefix/preamble | Clang-native serialized prefix state | Validated prefix/invocation and transitive inputs. |
| PCH | Clang's native precompiled header format | The exact compatible build/use contract. |
| Header module PCM | Module-map-defined compilation unit | Declared module environment and validated imports. |
| Standard C++ BMI | Named module/interface unit | Its own module graph and compiler compatibility rules. |
| Object/result | Full compilation result | Complete action inputs, outputs, and current cache policy. |

Clang PCH serialization includes preprocessor state as well as AST information and uses lazy loading. Reusing serialized bytes is distinct from sharing mutable deserialized compiler objects. [S02](05_sources_and_evidence.md#s02)

**V1 implementation boundary:** raw resources, complete dependency observations, object actions, controlled PCH prefixes, and explicitly supported modules. General arbitrary-header token replay is a later qualified optimization, not a prerequisite for useful caching.

## 2. Model preprocessing as a state transition

For design purposes:

```text
Preprocess(header_bytes, input_state, snapshot_fs, compiler_context)
    -> emitted_tokens, source_maps, diagnostics, output_state, dependency_evidence
```

`input_state` can include macro definitions/undefinitions, include stack, include-guard/once state, current logical source location, line-control state, pragma stacks, language extensions, stateful builtins, and relevant header-search context. The provider defines the complete state for each supported boundary.

A cached token string is insufficient when processing also defines macros for subsequent code, changes diagnostic/packing state, emits module imports, or advances a builtin counter. If replay cannot reproduce the complete supported transition, use a native PCH/module/prefix boundary or process normally with no semantic cache.

**Parsing is a separate issue.** Identical header text under identical preprocessor macros can be parsed under different previously declared types, namespaces, linkage, or packing state. A preprocess key is not a universal AST key. Probe P08 demonstrates a preceding typedef changing the same header's structure size. Do not transplant declarations from one Clang `ASTContext` into another by pointer. [Probe results](evidence/probe_results.md)

## 3. Identity hierarchy

Reuse the existing canonical identity machinery from the prior Simple plan. These are conceptual typed records, not a new incompatible hashing framework:

```text
CompilerContext = H(exact provider/toolchain/runtime closure,
                    target/ABI, language mode, driver semantics, SDK/sysroot,
                    relevant options, resource format)

InvocationContext = H(ordered real arguments, response-file closure,
                      meaningful environment, logical working directory,
                      forced-include sequence, BuiltinEnvironment,
                      effective project predefinitions)

PolicyContext = H(effective target/header rules, protected profile,
                  exception scope/review version, evaluator capability)

CandidateFamily = H(resource kind, header/module identity,
                    CompilerContext, PolicyContext)

ResourceKey = H(CandidateFamily, qualified input/context manifest)

ActionKey = H(complete computation inputs, invocation/toolchain,
              consumed resources, applicable computation/cache policy)
```

An observed candidate-family lookup is only a search index. It never authorizes a hit. Branch names, group PIDs, retry numbers, cache paths, and queue priorities are not semantic resource identity. Diagnostics, output path effects, working-directory interpretation, and option ordering cannot be dropped merely because they seem operational.

Policy changes must invalidate or require revalidation of previous admission evidence. V1 includes the effective policy root in the governed cache identity for simplicity. Later reuse across policies is permitted only via an explicit re-admission step proving the old artifact satisfies the new obligations. A timestamp or a different SDN rendering is not such a proof.

## 4. Strict mode versus complex mode

### Strict mode

Enforce the profile/variation domain. Keep all remaining required context in the key. For a controlled module, its isolated build environment naturally supplies a smaller boundary. For a textual include, strict macro declarations do not erase include-order or prior semantic state.

Begin with conservative matching. A declared variant is included even when a previous callback trace did not show an expansion. “Unused in one build” is not the same as “cannot influence this resource”.

### Complex mode

Allow only the approved additional variability, then select a **complete supported context**, not just a bigger list of `-D` strings. Initial complex mode operates at full TU/object or compatible native prefix/PCH boundaries. It can share raw bytes and validated native artifacts without implementing arbitrary AST-fragment reuse.

Where the provider can serialize and restore a complete header preprocessing boundary, include its full state. Where it cannot, `complex` falls back to the registry's explicit `none` or error outcome. Do not produce a “complete” certificate with unknown state fields.

A future observed-dependency mode can reduce the context only after the provider has a qualified completeness contract. Treat this as a separately versioned capability with independent rollback; it is not silently enabled by setting `complex`.

## 5. Safe two-stage lookup

1. Resolve the exact source/build snapshot, toolchain profile, and protected effective policy.
2. Evaluate entry-definition and declared-file rules before any whole-action cache shortcut.
3. Determine the effective scope/eligibility. For a first build or incomplete history, scan/execute conservatively; do not invent an input manifest.
4. Find candidate dependency manifests using `CandidateFamily`.
5. Validate each candidate's source digests, used resources, ordered resolution witnesses, positive and negative macro state, relevant builtin/pragma/prefix state, and rule evidence against the current snapshot.
6. Accept only a qualified complete match. Otherwise run the native provider, collect complete evidence, and classify any policy violations independently of cache misses.
7. Stage result payloads privately; publish only after validation of payloads, state contract, ownership fence, and admission policy.

Cold scans and cache-hit validation must use the same snapshot filesystem. If inputs can change between the scan and compile, either restart with a new snapshot or reject publication. Never hash the file then parse different bytes from a live checkout.

For full-context V1, a conservative immutable tree root and complete invocation can replace missing fine-grained witnesses at the cost of fewer hits. It must cover all accessible input roots, including SDK and generated data, not only the Git source tree.

## 6. Positive and negative macro dependencies

A sound reduced read set includes more than expanded macro names:

- A macro expanded or tested through `defined`, `#ifdef`, `#ifndef`, or a conditional expression.
- A macro that was **absent** when an identifier was eligible for expansion.
- Names formed through expansion/token pasting and rescanning.
- Definitions consulted in directive arguments, include names, pragmas, and feature tests.
- Incoming state that changes which branch or include is reached.

Counterexample:

```c
/* api.h */
int FIELD_NAME;
```

A previous build without `FIELD_NAME` as a macro has no successful expansion for that name. A later `-DFIELD_NAME=renamed` changes the tokens. Reusing the old header solely because its “expanded macro list” was empty is wrong. Probe P02 reproduces this.

Clang `PPCallbacks` supplies useful observations for macro definitions/expansions, conditionals, file inclusion/skips, pragmas and include probes. Its callback surface is not by itself a certificate that every failed expansion lookup was captured. The provider must either instrument the additional compiler/VFS points or retain the full relevant macro/context root. [S03](05_sources_and_evidence.md#s03)

Do not use a regex scanner, `-dM`, ordinary depfiles, or a previous positive-use log as the sole authority for dropping inputs from a key.

## 7. File resolution witnesses

Capture the identity and order of include directories, `-iquote`/system/framework roots, sysroot/resource directory, VFS overlays, and logical current directory. For each resolution query record selected identity and the relevant preceding candidates that were absent. Include `__has_include`, `__has_include_next`, conditional generated headers, `#include_next`, and supported binary embed directives.

A negative witness may be backed by a verified immutable directory/tree snapshot instead of enumerating every missing path. The witness must still change when a newly created higher-priority candidate changes resolution.

Probe P04 found an optional header absent from an ordinary dependency list; creating it changed preprocessing. Probe P05 confirmed include-path order changes the selected header. These show why content hashes over only previously successful includes are insufficient.

## 8. Special state and unsupported boundaries

| Case | Default handling |
|---|---|
| `__FILE__`, `__LINE__`, line directives | Record logical mapping/context; do not normalize away observable strings. |
| Date/time builtins | Use a declared reproducible build-time input when supported; otherwise no semantic reuse at the affected boundary. |
| `__COUNTER__`, include level/base-file state | Capture incoming state and output effect, or use a larger supported boundary/no cache. |
| `#pragma pack`, diagnostics, push/pop macro | Native provider state/replay; reject an incomplete key or unsupported replay. |
| Header guards / `#pragma once` | Preserve identity and prior-inclusion behavior, not a global “skip this name” map. |
| Repeated X-macro `.inc/.def` | Explicit textual-fragment contract; each invocation keeps its context. |
| Header defining macros used afterward | Include outgoing macro effects in the boundary artifact or retain native textual processing. |
| Unknown pragma, plugin, extension or environment read | Conservative complete action/isolated mode; no precision claim. |
| Generated/optional file | Producer edge plus snapshot-bound presence/absence. |
| Header units, Clang header modules, named C++ modules | Separate resource kinds and provider contracts; no cross-kind substitution. |

Standard date/time and source-location macros have observable expansion behavior; the design treats them as explicit inputs rather than a generic “ignore volatility” flag. [S14](05_sources_and_evidence.md#s14) The locally tested counter state and packing examples are in P07/P09.

No-cache annotations must be checked when composing a PCH/module. Reject creation of a reusable aggregate that embeds a forbidden semantic boundary. An ordinary textual include stays outside that aggregate, or the aggregate becomes uncached.

## 9. Macro variants and ABI/ODR domains

Build different header resources for allowed macro values, but also identify public compatibility domains. For a boundary whose layout, calling convention, enum values, inline/template definitions, or public constants must agree across translation units, attach the appropriate interface/semantic contract to consuming and producing artifacts.

Before linking, validate required domain constraints. `PROJECT_ABI=3` in one public library and `PROJECT_ABI=4` in a consumer must not be accepted just because both compilations were individually cached correctly. A macro affecting only a task-private implementation need not force every object to use the same value.

Do not claim a general C++ ODR proof from macro equality alone. V1 enforce explicitly declared compatibility domains; later add compiler-derived public semantic witnesses where available. Tests and ABI tools supplement, not replace, these declared contracts.

## 10. ResourceShare extension

Retain the prior split:

```text
ResourceStore: immutable payloads and verified mappings
ResourceState: mutable single-flight records, readiness, ownership, leases
CompilerProvider: context capture, compatibility checks, native produce/consume
ExecutionContext: snapshot filesystem, output sink, diagnostics, cancellation
```

Add a `HeaderPolicyEvaluator`, `PreprocessObservation`, `HeaderCompatibilityWitness`, and `CacheEligibility` to the existing provider contract. Do not expose Clang objects as cross-process wire data.

Proposed operations:

```text
classify_boundary(request, policy) -> eligibility + obligations
capture_or_validate_context(request, candidate?) -> complete witness | unknown
acquire_resource(key, witness) -> pinned descriptor | need producer
produce_native_resource(action_context) -> candidate + observation
validate_resource(candidate, witness, current_policy) -> admitted | rejected
compile_with_resources(private_context, pinned_resources) -> outputs
```

SDN carries declarations/manifests/diagnostics; binary carries PCH/PCM/object data and qualified shared mappings. In-group calls use ordinary typed APIs, not an SDN round trip on every lookup.

## 11. Grouped execution and modifiable startup data

A mid-scheduler process can retain mutable source indexes, dependency observations, single-flight state, and allocator pools shared by compile threads. Index entries point to verified immutable payloads. Give each request its own preprocessing/AST context and diagnostics; do not leave macro tables from one request in another's scratch context.

The group identity includes exact provider/toolchain ABI, runtime and trust class, and process-global option constraints. Header variants are resource identities; do not start a new process for every `FEATURE_LOG` value unless the provider's global-state limitations require it.

Across groups, map the same immutable resource bytes where compatible. Keep authoritative publication state outside crash-prone groups. A writable shared index needs explicit owner-death/generation recovery; a corrupt group must not overwrite the scheduler's ledger.

Clangd's documented distinction—immutable preambles versus non-thread-safe live ASTs—supports this serialization boundary, not unlimited frontend reentrancy. Qualification is still required for the exact provider. [S06](05_sources_and_evidence.md#s06)

## 12. Single-flight and retry

One owner builds a resource under `(key, attempt, group_epoch, fence)`. Waiters release compiler execution tokens while awaiting dependencies; module construction cannot be trapped behind every waiting TU. Distinct macro variants never share the same construction slot.

Publish `READY` only after bytes, format, complete witness, and policy are validated. A producer crash leaves no partially readable result. Retire its epoch and rebuild under a new attempt. A canceled waiter does not cancel shared work needed by another request.

Policy violations and macro mismatches are deterministic failures: **do not retry them uncached to make CI green**. A legitimate cache incompatibility is a miss and rebuild. A provider crash permits the bounded isolated recovery in the prior plan. An isolated rerun must retain the same policy, input context, and variant; retries may not silently strip flags or substitute SDKs.

If complete equal keys for a declared deterministic/cacheable action produce different tokens/artifacts, quarantine the affected mapping/provider path and preserve a reproducer. Intentionally nondeterministic no-cache actions instead retain per-attempt output evidence and do not populate the successful reusable mapping. Hash validity proves byte identity, not correctness of an incomplete key.

## 13. Performance program

Prefer the lowest-risk wins first: immutable file sharing, warm provider processes, single-flight PCH/module production, and action cache reuse. After that, use incremental persistent macro-state hashing or native cached environment fingerprints to avoid serializing large maps at every header boundary.

Compute builtin/profile roots once per exact configuration, not once per token. Keep counters for bytes parsed, headers expanded, native artifacts deserialized, trace/validation CPU, lock contention, variant count, miss causes and evictions. Bound variants per resource and total resident mappings. Exceeding a budget can select an already-approved no-cache path or report exhaustion, but must never merge unequal variant keys.

Use observed workloads to rank prewarm candidates; do not prebuild the Cartesian product of all macros. Measure cold/warm, strict/full-context/qualified-precision, isolated/grouped, and local/remote separately. The sub-minute preflight objective remains an objective for eligible warm workloads, not a reason to remove validation.
