# Final report — Simple / Clang strict header and preprocessor caching

**Date:** 2026-09-25  
**Status:** Final design proposal with executed native counterexample probes. This is not an implemented or benchmarked Simple feature.  
**Core rule:** Unexpected project predefinition/context variation is an error. Declared variants and reviewed macro/file exceptions may permit it, but reusable resources must still include complete semantic inputs. An exception selects complete-context caching or no semantic reuse—not an ignored input.

## Contents

1. [Strict macro and header variation policy](#report-1)
2. [Cache engine and resource sharing](#report-2)
3. [Clang library provider and CMake/Ninja integration](#report-3)
4. [CI, tests, recovery and implementation](#report-4)
5. [Sources and evidence limitations](#report-5)
6. [Actual local probe results](#local-probes)

The companion ZIP also includes separate Markdown reports, policy recipes, an illustrative SDN registry, the executable probe script/logs, and unchanged copies of the earlier build-platform reports. The new extension adds 56 planned acceptance scenarios; only the 12 native counterexample probe groups were executed. No repository, hook, or GitHub setting was changed.

---

<a id="report-1"></a>

# Report 1 — Strict macro and header variation policy

**Project:** Simple build platform / Clang provider  
**Date:** 2026-09-25  
**Status:** Final design proposal for implementation; not an implemented Simple feature. All new commands, schemas, and diagnostics are proposed.  
**Scope:** Extend the previous build/CI plan with explicit preprocessing variation contracts. Preserve SDN, grouped compiler processes, resource sharing, and qualified isolated fallback.

## 1. Decision

Make unexpected preprocessing variation a **build-policy error**, not merely a reason to miss the cache. Permit variation only through an explicit macro domain, an approved configuration-file provider, or a narrowly scoped exception. Every exception must select **complex caching** or **no semantic cache**; none may silently exclude a semantic input from cache identity.

The contract has three distinct questions:

1. Is this definition, file, or contextual change **permitted**?
2. Does the provider have sufficient evidence to **reuse** a particular resource?
3. Is the resulting artifact **compatible** with its consumers and linked peers?

A “yes” to one question does not imply “yes” to the other two. In particular, allowing two macro values does not make their PCHs interchangeable, and separate valid object caches do not make two conflicting ABI configurations link-compatible.

## 2. Policy model

| Policy | Allowed variability | Reuse rule | Failure behavior |
|---|---|---|---|
| `strict-fixed` | Only the reviewed fixed environment for this profile | Exact compatible resource context | Unexpected change is an error, even on a cold cache. |
| `strict-variants` | Only named macros and admitted definition states/values | Distinct variants plus all other required context | An unknown macro or out-of-domain value is an error. |
| `complex` | Specifically approved open-ended or contextual variation | Conservative complete context; use a supported boundary | Incomplete context disables reuse or errors according to the explicit fallback. |
| `none` | Variation allowed only by its matching exception/profile | Do not read/write semantic caches for the governed boundary | Compile normally; still report source errors and other policy violations. |

`strict` describes enforcement, not an unsafe small hash. A strict resource can still require a large key until a smaller dependency projection is certified. `complex` does not mean “accept any input anywhere”; the scope of the allowance remains narrow.

Use separate fields for `variation_permission` and `cache_mode`. This prevents `cache_mode: none` from unintentionally authorizing an unrelated forbidden definition. The convenient configuration form may specify both in a single exception row, but the evaluator must keep their meanings distinct.

## 3. What counts as a predefined macro

Maintain three layers rather than one unstructured map:

**Toolchain environment.** Compiler-generated definitions derived from the exact executable/libraries, target ABI/CPU, language dialect, SDK/sysroot, and relevant driver options. Record them as a verified `BuiltinEnvironment` root. Developers do not hand-register thousands of compiler builtins. An unsupported toolchain/target profile is rejected; an approved different profile gets a different identity. Do not compare x86 and ARM builtins as though they were accidental project changes.

**Project entry definitions.** Effective `-D`, `-U`, response-file options, approved driver/config-file contributions, and forced-include/`-imacros` configuration before the main source. Compare these against the target/configuration registry. Extra, removed, or changed entry definitions outside approved rows are errors by default, whether or not a particular header currently consumes them.

**Source-local and header-entry state.** Definitions made by actual source/header directives. An ordinary internal `#define` does not require one global registry entry per occurrence. A macro crossing into a reusable header boundary becomes a contextual input. Its origin, use, and allowed parameterization must be recorded or conservatively routed through a declared complex/textual boundary. Generated include guards are lifecycle state, not user-configurable feature variants; their behavior must nevertheless be preserved by the provider.

A final `clang -dM` dump is useful evidence, not a complete account of preprocessing: it does not preserve all definition history, search probes, pragma state, or contextual builtins. Capture the real invocation and provider observations as well.

## 4. Definition identity is more than a string value

Represent each definition using a provider-versioned structure:

```text
MacroDefinitionIdentity:
    name
    state = undefined | object_like | function_like | builtin
    replacement tokens, including semantically relevant spelling/spacing
    parameter list and variadic form
    origin kind and source/snapshot location
    builtin evaluator identity, when applicable
```

Do not merge `undefined`, `defined as 0`, `defined empty`, and `defined as 1`. Do not evaluate numeric spellings and then assume equal arithmetic values mean equivalent macros: stringification can expose the spelling. Do not sort command-line `-D/-U` operations; preserve their original order and the compiler's resulting environment. Macro stringification and token-pasting also require dependencies introduced by expansion, not just lexically visible names.

Policy value matching uses the declared definition-state/token contract plus an authorized origin scope. A changed source line number is not by itself an illegal new macro value; origin locations support diagnostics and context evidence, while ordinary source edits update input identity.

The local probes P01–P03 demonstrate these distinctions using the installed Clang. They test language behavior, not the proposed cache implementation. [Probe results](evidence/probe_results.md)

## 5. Fixed and varying definitions

An example product profile might specify:

| Macro | Contract | Example accepted states |
|---|---|---|
| `PROJECT_ABI` | Fixed and link-domain invariant | object-like `3` only |
| `FEATURE_LOG` | Declared resource variant | object-like `0` or `1` |
| `NDEBUG` | Declared profile variant | undefined or object-like `1` |
| `BUFFER_LIMIT` | Declared bounded variant | Explicit token spellings for 256, 512, 1024 |
| `VENDOR_BUILD_TEXT` | Scoped exception | Arbitrary replacement under `vendor/legacy/`, complex mode |
| `BUILD_WALLCLOCK` | Scoped exception | Dynamic/unmodeled value, no semantic cache |

Changing `PROJECT_ABI` requires a reviewed profile/ABI migration. A vendor-file exception cannot override an unrelated global ABI invariant. Do not generate the “fixed” baseline afresh from every invocation: that would bless the very unexpected variation the policy is intended to catch.

Profile inheritance must be explicit and acyclic. Common defaults can be shared; overlapping conflicting rules produce a configuration error rather than depending on hash-map iteration or “last file wins”.

## 6. Configuration-file registration

Register a file in one of these roles:

| Role | Meaning |
|---|---|
| `configuration-provider` | Supplies named or reviewed sets of macro definitions, such as a generated `config.h`. |
| `strict-header` | Ordinary reusable header governed by fixed/variant rules. |
| `complex-header` | Approved contextual boundary; complete context is retained. |
| `no-cache-header` | Textual processing is required and semantic reuse is prohibited for its boundary. |
| `textual-fragment` | Repeated-inclusion/X-macro fragment that is not a standalone module or AST cache unit. |

A provider record binds resolved path/root, source or producer identity, output digest, allowed exported macro names, target/configuration scope, include/force-include order, and owner. A file being “registered” does **not** mean its bytes may be ignored. If a generated configuration header changes, its dependent preprocessing resources must rekey.

For normal project headers, register approved ownership roots and apply strict defaults; individual declarations are needed for exceptions and special boundaries, not every routine header. An input outside all approved project/dependency/toolchain roots is rejected or explicitly onboarded.

Matching uses normalized logical paths within an immutable snapshot plus verified resolution. Prevent `..`, symlink escapes, case-folding collisions, and a same-named shadow header from acquiring another file's exception. Third-party/submodule rules bind the pinned dependency identity, not an arbitrary writable absolute path.

## 7. Scope exceptions by both macro origin and consumer

A safe exception can match:

```text
macro = VENDOR_BUILD_TEXT
origin = vendor/sdk/config.h
consumers = vendor/sdk/**
action = allow variation using complex cache
```

The origin alone is insufficient. If that macro later changes the meaning of a strict project header, the exception must not automatically spread. Record the dependency where the value is consumed. Conversely, matching the consumer alone must not allow a malicious unrelated file to impersonate the registered provider.

A file-wide exception may intentionally allow any entering project macro variation **for that file**, but must select complex/full-context or none. If entry definitions are otherwise forbidden at invocation scope, such a waiver is provisional until complete dependency evidence proves that their effects stay inside the approved scope. When that confinement cannot be established, broaden the explicitly approved action scope or reject; never assume confinement from an old positive-use trace.

Allow a separate explicit action-level legacy profile when a vendor build genuinely cannot be classified narrowly. It must carry a stronger review requirement, exact input tracking or no-cache status, and an expiry/migration owner. It is not the default for the whole repository.

## 8. SDN authoring contract

The following is an **illustrative SDN table schema**, consistent with the table-oriented style in the preceding reports. Its exact parsing has not been validated against Simple. Placeholder digests are invalid for production admission.

```sdn
schema |name, version, example_only|
    "simple.header_policy", 1, true

profile |id, entry_definitions, unregistered_inputs, default_cache|
    "host-cxx", "strict", "error", "strict"

fixed_macro |profile, name, state, replacement, compatibility|
    "host-cxx", "PROJECT_ABI", "object_like", "3", "must_match_link_domain"

variant_macro |profile, name, state, replacement|
    "host-cxx", "FEATURE_LOG", "object_like", "0"
    "host-cxx", "FEATURE_LOG", "object_like", "1"
    "host-cxx", "NDEBUG", "undefined", ""
    "host-cxx", "NDEBUG", "object_like", "1"
    "host-cxx", "BUFFER_LIMIT", "object_like", "256"
    "host-cxx", "BUFFER_LIMIT", "object_like", "512"
    "host-cxx", "BUFFER_LIMIT", "object_like", "1024"

configuration_file |profile, path, producer, exported_set|
    "host-cxx", "build/generated/config.h", "//config:generate", "project-config-v1"

exported_macro |set, name|
    "project-config-v1", "FEATURE_LOG"
    "project-config-v1", "BUFFER_LIMIT"

exception |id, macro, origin, consumers, permission, cache, incomplete|
    "vendor-text", "VENDOR_BUILD_TEXT", "vendor/sdk/config.h", "vendor/sdk/**", "allow_variation", "complex", "none"
    "build-time", "BUILD_WALLCLOCK", "build/generated/time.h", "src/build_info.c", "allow_variation", "none", "none"

file_rule |id, path, role, permission, cache, ancestor_reuse|
    "rows", "include/detail/rows.inc", "textual-fragment", "allow_scoped_context_variation", "none", "forbid_semantic"
    "legacy-api", "vendor/legacy/generated_api.h", "complex-header", "allow_scoped_context_variation", "complex", "validated_context_only"

exception_review |id, owner, reason, expires|
    "vendor-text", "toolchain", "External SDK emits unconstrained build text", "2026-12-31"
    "build-time", "release", "Deliberately dynamic build-information source", "2026-12-31"
    "rows", "compiler", "Repeated include under caller-supplied ROW macro", "2026-12-31"
    "legacy-api", "toolchain", "Legacy header uses contextual configuration", "2026-12-31"
```

Here `configuration_file` only recognizes the provider; it does not by itself allow unlimited values. Exported values still satisfy fixed/variant/exception rules. For generated source, resolve the producer action and materialize its exact result before evaluating the configuration.

The evaluator combines applicable strict obligations; exceptions discharge only the exact named violation classes they cover. An explicit `none` dominates cache eligibility. A `complex` exception prevents strict reuse unless strict compatibility is independently established. A fixed ABI conflict remains an error unless the protected profile itself is deliberately migrated.

## 9. Diagnostics

An unexpected entry definition should produce a diagnostic even when no cache file exists:

```text
E-HCACHE-UNDECLARED-VARIATION
  target: //app:demo
  profile: host-cxx
  macro: FEATURE_FAST
  expected: absent from admitted entry environment
  actual: object_like "1"
  origin: response file build/flags.rsp, argument 12
  affected boundary: include/project/api.h
  policy: config/build/header_policy.sdn
  cache decision: no resource/result admitted
  remedies: declare a supported variant; fix the invocation;
            or add a reviewed scoped complex/no-cache exception
```

Use distinct codes for invariant mismatch, unsupported domain value, undeclared provider file, ambiguous policy, incomplete dependency evidence, unsupported cache boundary, conflicting ABI/ODR domain, and unsafe ignore flags. Include old/new definition identities, include chain, matched policy IDs, and the proposed invalidation scope. Do not “repair” code by silently changing its `-D` flags.

A normal changed header within an admitted source snapshot is usually a **cache miss**, not a policy error. The error is unapproved variation or an invalid contract. This avoids turning ordinary edits into permission requests.

## 10. No-cache means no semantic shortcut

The default `none` contract applies transitively to semantic resources that would otherwise hide processing of the governed input. A cached PCH/PCM/preamble containing the header is not exempt because the header itself was marked uncached. Neither may an old whole-TU object cache hit bypass that requirement.

Default behavior:

- Read/write no reusable expanded-header, serialized-header, enclosing-prefix, or enclosing-TU result entries that bypass the input.
- Reprocess the affected translation unit under the actual admitted context on every requested build of that target.
- Retain immutable raw source transport/storage only when content-storage policy permits; raw byte sharing is not a parsed-result hit.
- Allow downstream link/test reuse only after current fresh producers have supplied actual complete inputs and their own determinism/validation rules permit it. Never take an ancestor shortcut while fresh production is still required.

An advanced `resource-only` opt-out may permit whole-action reuse, but must have a separate explicit name and documentation. It is not the meaning of plain `none`. Confidentiality rules such as “never persist this file” are another independent policy and can prohibit raw storage too.

## 11. Existing Clang support is a foundation, not the full policy

Clang module maps provide `config_macros`; their documented implementation uses a limited check for configuration changes, and the `exhaustive` optimization is not implemented as a general verifier. Therefore the project-wide strict allowlist is a Simple policy layer, not a promise that adding one Clang flag implements this design. [S01](#s01)

Do not map exceptions to `-fmodules-ignore-macro`. That flag is intended for macros that do not influence the module; allowing a macro to vary is a different statement. Preserve ordinary compiler validation and reject cache-weakening flags that conflict with the policy.

## 12. Acceptance rule

An admitted cache hit requires all of: permitted variation, complete matching inputs/context, supported resource boundary, verified bytes/manifest, valid producer provenance, and current policy evidence. Failure of any condition cannot become a successful strict hit.

The policy evaluator must be deterministic between cold/warm caches, local/remote workers, and grouped/isolated execution. Performance changes implementation cost, not the contract.


---

<a id="report-2"></a>

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

Clang PCH serialization includes preprocessor state as well as AST information and uses lazy loading. Reusing serialized bytes is distinct from sharing mutable deserialized compiler objects. [S02](#s02)

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

Clang `PPCallbacks` supplies useful observations for macro definitions/expansions, conditionals, file inclusion/skips, pragmas and include probes. Its callback surface is not by itself a certificate that every failed expansion lookup was captured. The provider must either instrument the additional compiler/VFS points or retain the full relevant macro/context root. [S03](#s03)

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

Standard date/time and source-location macros have observable expansion behavior; the design treats them as explicit inputs rather than a generic “ignore volatility” flag. [S14](#s14) The locally tested counter state and packing examples are in P07/P09.

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

Clangd's documented distinction—immutable preambles versus non-thread-safe live ASTs—supports this serialization boundary, not unlimited frontend reentrancy. Qualification is still required for the exact provider. [S06](#s06)

## 12. Single-flight and retry

One owner builds a resource under `(key, attempt, group_epoch, fence)`. Waiters release compiler execution tokens while awaiting dependencies; module construction cannot be trapped behind every waiting TU. Distinct macro variants never share the same construction slot.

Publish `READY` only after bytes, format, complete witness, and policy are validated. A producer crash leaves no partially readable result. Retire its epoch and rebuild under a new attempt. A canceled waiter does not cancel shared work needed by another request.

Policy violations and macro mismatches are deterministic failures: **do not retry them uncached to make CI green**. A legitimate cache incompatibility is a miss and rebuild. A provider crash permits the bounded isolated recovery in the prior plan. An isolated rerun must retain the same policy, input context, and variant; retries may not silently strip flags or substitute SDKs.

If complete equal keys for a declared deterministic/cacheable action produce different tokens/artifacts, quarantine the affected mapping/provider path and preserve a reproducer. Intentionally nondeterministic no-cache actions instead retain per-attempt output evidence and do not populate the successful reusable mapping. Hash validity proves byte identity, not correctness of an incomplete key.

## 13. Performance program

Prefer the lowest-risk wins first: immutable file sharing, warm provider processes, single-flight PCH/module production, and action cache reuse. After that, use incremental persistent macro-state hashing or native cached environment fingerprints to avoid serializing large maps at every header boundary.

Compute builtin/profile roots once per exact configuration, not once per token. Keep counters for bytes parsed, headers expanded, native artifacts deserialized, trace/validation CPU, lock contention, variant count, miss causes and evictions. Bound variants per resource and total resident mappings. Exceeding a budget can select an already-approved no-cache path or report exhaustion, but must never merge unequal variant keys.

Use observed workloads to rank prewarm candidates; do not prebuild the Cartesian product of all macros. Measure cold/warm, strict/full-context/qualified-precision, isolated/grouped, and local/remote separately. The sub-minute preflight objective remains an objective for eligible warm workloads, not a reason to remove validation.


---

<a id="report-3"></a>

# Report 3 — Clang library provider and CMake/Ninja integration

**Date:** 2026-09-25  
**Status:** Proposed integration plan. The native-tool probes in `evidence/` are executed examples; the Simple launcher/provider commands below are not implemented by this report.

## 1. Corrections and final decisions

| Earlier simplification | Final integration rule |
|---|---|
| A Clang dynamic library is inherently faster. | Persistent lifetime and resource reuse are the main benefits. Compare dynamic and static provider builds under the same lifetime. |
| CMake File API supplies the complete executable build DAG. | Use it for target/configuration metadata; retain Ninja for exact native execution until an execution adapter is complete. |
| A compilation database is enough to rebuild a project. | It describes compile invocations, not all generator, link, install, test, and dynamic-dependency actions. |
| A compiler launcher enforces every build request. | It runs only when the underlying builder invokes a compilation; policy-only/no-cache work needs explicit top-level validation and invalidation. |
| A list of varying macros is sufficient for every header AST. | Header context can include previous semantic declarations; use native serialization boundaries or textual processing. |
| A vendor exception can ignore a macro in the key. | The exception must retain complete context or disable semantic reuse. |

Use **CMake + Ninja + Simple compiler launcher + SDN policy + optional File API metadata** as the first production integration. This requires no new CMake generator and no initial Ninja reimplementation.

## 2. Clang as a library: what exists

Upstream defines a `clang-cpp` shared-library target assembled from Clang components; its build requires the relevant PIC support and has platform-specific linking details. This establishes an available integration substrate, not a complete Simple provider. [S04](#s04)

`libclang` supplies a deliberately limited stable high-level C interface. Full frontend/preprocessor control needs the C++ implementation interfaces or a tailored adapter, whose API evolution must be managed. [S05](#s05)

Recommended boundary:

```text
Simple group/mid-scheduler
    -> stable, versioned Simple C ABI
        -> pinned C++ adapter
            -> clang-cpp OR statically linked Clang components
                -> private compiler/frontend contexts per request
```

The wrapper exports lifecycle, invocation creation, policy observation, dependency capture, native resource production/consumption, compilation, cancellation, and result collection. No `std::string`, `ASTContext*`, C++ exception, or allocator ownership crosses the external ABI. Use explicit byte spans, opaque scoped handles, status codes, and release functions.

Pin the adapter, Clang/LLVM libraries, runtime, resource directory, and serialization schema together by digest. “Clang major version matches” is not sufficient binary compatibility. Separate incompatible versions into different group processes; do not load several conflicting LLVM copies into the trusted scheduler.

## 3. Dynamic versus static provider packaging

A shared `clang-cpp` provider is convenient for initial implementation and independent toolchain distribution. A static-component provider may provide better optimization or deployment characteristics. Both can be persistent and both can use shared binary resources.

LLVM distribution guidance warns against using `BUILD_SHARED_LIBS=ON` to make every component a shared library. It recommends its consolidated LLVM-dylib mechanism where supported; that mechanism is documented as unavailable on Windows. Therefore a Linux recipe cannot be presented as a universal Windows DLL recipe. [S07](#s07)

A **non-executed, Linux-oriented build template** for a pinned source tree is:

```sh
cmake -S /src/pinned-llvm-project/llvm -B /build/clang-provider -G Ninja \
  -DCMAKE_BUILD_TYPE=Release \
  -DLLVM_ENABLE_PROJECTS=clang \
  -DLLVM_ENABLE_PIC=ON \
  -DBUILD_SHARED_LIBS=OFF \
  -DLLVM_BUILD_LLVM_DYLIB=ON \
  -DLLVM_LINK_LLVM_DYLIB=ON \
  -DCLANG_LINK_CLANG_DYLIB=ON
cmake --build /build/clang-provider --target clang-cpp clang clang-scan-deps
```

Resolve options and exported targets against the selected LLVM revision. For Windows, qualify the available `clang-cpp`/runtime packaging or use a private provider DLL/executable statically linked to the necessary components behind the same Simple C ABI. This report does not build or test either shared-library package.

Benchmark fresh CLI, warm singleplex, dynamic-library group, and static-library group. Do not credit OS-shared executable pages as an advantage unique to dynamic linking; do not claim a numeric speedup without measurements.

## 4. Header-policy enforcement adapter

The adapter must receive the real resolved driver invocation, not a reconstructed command containing only include directories and definitions. Preserve compiler selection, target, response files, `-D/-U` ordering, forced includes, CWD interpretation, environment, resource paths, diagnostic modes, and all produced side files.

Install provider observations before preprocessing. At each supported resource boundary, evaluate the policy and build/validate its context witness. On a PCH/module hit, validate the resource's stored policy/observation evidence; callbacks for an already materialized resource may not repeat every original event.

A frontend plugin can be an incremental way to emit project diagnostics and manifests, but **does not automatically provide complete failed-lookup or arbitrary replay instrumentation**. Maintain a capability matrix per pinned provider. Unsupported precision stays full-context, isolated, or no-cache rather than claiming completeness.

The early useful mode is an external Clang process with policy validation and explicit PCH/module actions. The later in-process mode uses the same action/resource contract. A preprocessor-only pass is not sufficient to execute code generation; the C++ wrapper must create the appropriate compilation action and return all expected outputs.

## 5. Native resource boundaries

Use `target_precompile_headers()` for suitable CMake-managed prefixes. CMake documents that `REUSE_FROM` requires matching compiler options, flags, and definitions; unrelated targets must not share a PCH just because their header list matches. It also provides target/source controls for disabling PCH use. [S10](#s10)

For Clang header modules, admit a reviewed module map and isolated module build environment. For standard C++ modules, keep their explicit dependency graph and native provider kind; do not equate them with header modules or a general `#include` result. [S13](#s13)

Do not transform arbitrary textual includes into imports merely to gain speed. A non-modular header may rely on caller macros, repeated inclusion, or surrounding declarations. Register it as a textual/complex boundary or leave it uncached. Use the strict policy to identify such boundaries, not to silently alter source semantics.

## 6. CMake launcher path: first implementation

CMake's `<LANG>_COMPILER_LAUNCHER` property supports launcher commands with Makefile/Ninja generators. The launcher is passed the compiler and its arguments, enabling the external tool to delegate or distribute compilation. [S08](#s08)

Illustrative setup once `simple cc-launch` exists:

```sh
cmake -S . -B build/simple -G Ninja \
  -DCMAKE_C_COMPILER=/toolchains/pinned/bin/clang \
  -DCMAKE_CXX_COMPILER=/toolchains/pinned/bin/clang++ \
  -DCMAKE_EXPORT_COMPILE_COMMANDS=ON \
  '-DCMAKE_C_COMPILER_LAUNCHER=/tools/simple;cc-launch;--policy;/project/config/header_policy.sdn;--' \
  '-DCMAKE_CXX_COMPILER_LAUNCHER=/tools/simple;cc-launch;--policy;/project/config/header_policy.sdn;--'
cmake --build build/simple
```

The last command alone gives launcher interception for native dirty compiles. The complete Simple policy requires the top-level preflight/driver described next. Paths are examples, and the Simple subcommand is proposed.

The launcher must preserve the compiler contract: correct exit status, per-action diagnostics, `.o/.obj`, dependency outputs, split debug files, module outputs, and platform-specific auxiliary outputs. Capture all declared results atomically. Treat unknown side effects as unsupported rather than returning a fake object-cache success.

It must not recursively relaunch itself. Record an invocation identity; unwrap only explicitly recognized launchers. Nesting Simple with ccache/sccache is disabled by default because an outer or inner cache can bypass policy/observation. A qualified stacked mode needs a precise ordering and complete evidence contract.

## 7. Crucial gap: Ninja may never call the launcher

The local integration probe configured a real CMake/Ninja project, ran it through a logging compiler launcher, then changed an undeclared policy file. Ninja considered the object up to date and **did not invoke the launcher**. Adding the file as an object dependency caused recompilation. [P11/P12 evidence](evidence/probe_results.md)

Therefore provide two controls:

**Top-level policy gate.** Every requested Simple build validates the current effective policy/profile and examines which previously accepted actions are still eligible. A native Ninja no-op is not sufficient admission evidence.

**Native invalidation bridge.** Add policy/profile/effective-input stamps as dependencies of governed native objects. In supported CMake Makefile/Ninja projects, `OBJECT_DEPENDS` can declare additional object prerequisites; it is not implemented by the Visual Studio/Xcode generators. [S11](#s11)

Minimal native example:

```cmake
# Real CMake syntax. The complete Simple helper is still proposed.
set_property(SOURCE main.cpp APPEND PROPERTY OBJECT_DEPENDS
  "${CMAKE_SOURCE_DIR}/config/header_policy.sdn")
```

For scalability, generate stable per-target/effective-policy stamps instead of rebuilding the repository after any unrelated exception edit. Write a stamp only after validating its inputs. When its content changes, the adapter must ensure native invalidation observes it; do not assume coarse timestamps or a preserved mtime prove content equality.

For a `none` resource, force the selected enclosing semantic action to run on each explicit build request, for example through a governed per-invocation dependency stamp. Merely declining a Simple cache hit is insufficient if Ninja already skipped the action. If the adapter cannot enforce the required dirty state, reject that cache policy in delegated mode or execute the selected action through the full Simple executor.

A direct bare `ninja` invocation without integration may be useful for development, but must not be advertised as producing the complete Simple policy receipt. CI uses the gate-enabled entry point. Do not force rebuilds by touching source files or silently weakening the registry.

## 8. File API and compilation database roles

Use CMake File API to label targets, configurations, source groups, compile settings, dependencies, toolchains and CMake-origin diagnostics. Its codemodel supplies optional compiler command fragments and related metadata; this is not an authoritative replay of every build action. [S09](#s09)

Use `compile_commands.json` for TU discovery and developer tooling. CMake supports exporting it for Makefile/Ninja generators; its presence does not establish all prerequisites or link/custom-command behavior. [S12](#s12)

Translate imported metadata to the Simple typed/SDN model. Keep JSON at the CMake boundary; the native protocol remains SDN. Record the File API object versions and reject unsupported required fields rather than assuming all installed CMake versions expose current online documentation.

At execution, the launcher-observed ordered invocation is authoritative for that compile. If its flags differ from the imported expectation, update/revalidate the graph or reject; never execute with a stale reconstructed command. Configuration-specific definitions are registered profiles, not an excuse to accept arbitrary per-file flag drift.

Do not try to evaluate `CMakeLists.txt`, generator expressions, `find_package()`, or platform probes in Simple. Let CMake configure. A cached configure result requires the complete probe/environment/package/tool closure and relocatability contract; hashing only `.cmake` source files is insufficient. Initially retain CMake's own reconfigure mechanism inside the tracked build adapter.

## 9. Generated files, configure probes and source snapshots

Generated configuration headers are producer outputs with explicit graph edges. The compiler cannot infer a current generated header from yesterday's file at the same path. The native bridge must order producer completion before scanning/compilation.

Configure-time compiler probes use an explicit `configure-probe` profile; they are not automatically authorized as final product artifacts. Scope any broader flexibility to that profile and do not let it publish product object-cache entries. Preserve the exact probe flags and toolchain even when no product target exists yet.

The Simple driver snapshots all declared inputs or validates them against a complete immutable view. Native Ninja is still timestamp-oriented; a same-mtime content change must be detected by Simple's digest-based planning and reflected into native dirty state. Delegation without this bridge is a compatibility mode, not a claim of authoritative content-based CI.

## 10. Ninja import: later full execution adapter

Keep a separate `NinjaAdapter` for projects generated by CMake, Meson, GN, or other tools. It is an execution-format adapter, not a replacement for configuration semantics.

Before claiming complete support, implement and test:

| Feature group | Required semantics |
|---|---|
| Parsing | Escaping, continuations, variable expansion, scope, `include` and `subninja`. |
| Graph | Explicit/implicit/order-only/validation dependencies, multiple outputs, phony/default targets. |
| Runtime dependencies | depfiles, supported `deps` behavior, dynamic `dyndep` updates and generated inputs. |
| Execution | Native shell/Windows command rules, response files, pools, console ownership, cancellation. |
| Incrementality | Command identity, `restat`, generator regeneration, missing outputs, build-file rebuild/reload. |
| Provider capture | Exact known compile actions and side files; no guessed arguments from command-string splitting. |

Ninja explicitly supports dynamically discovered inputs/outputs and updates its graph from dyndep files. Ignoring them can break first-build ordering. [S15](#s15)

On unsupported constructs, delegate the **complete necessary native graph boundary** or return unsupported. Do not execute an apparently safe subset while dropping its dependencies. Only one engine schedules a given graph boundary: Ninja may schedule native actions while the launcher handles each compile's internal resources; a future full Simple adapter replaces that role rather than racing it.

## 11. Final integration sequence

1. Implement the strict SDN registry and complete invocation capture against isolated Clang.
2. Add a CMake compiler launcher and an always-run policy gate with native dependency stamps.
3. Add explicit compatible PCH/module resource actions and the shared resource service.
4. Import File API metadata for ownership, profile mapping and diagnostics; keep native execution.
5. Qualify pinned C++/C-ABI library providers and grouped compilation against isolated behavior.
6. Implement complete Ninja execution support only where its maintenance cost is justified.

This sequence delivers useful header/resource reuse and distributed compiles without first implementing CMake or Ninja from scratch.


---

<a id="report-4"></a>

# Report 4 — CI, tests, recovery, and implementation plan

**Date:** 2026-09-25  
**Status:** Proposed implementation extension to the preceding Simple build-platform plan.  
**Evidence:** Twelve local counterexample probes ran successfully; the Simple cache/provider, SDN schema, and CI integration described here have not been implemented or executed.

## 1. Integrate the existing plan; do not create another gate system

Extend the previous plan's canonical SDN policy runner, action identities, ResourceShare contracts, and validation receipts. Keep the same main scheduler → node agent → grouped mid-scheduler processes → compile threads model. This report does not claim a new audit of the current Simple repository; the historical source findings in the supplied plan remain dated to their recorded commit.

The new header-policy gate has two independent outcomes:

- **Permission:** every relevant macro/file/context change is allowed by the selected protected profile or a matching reviewed exception.
- **Reuse eligibility:** every proposed cache hit has complete matching context, an admissible resource boundary, valid bytes, and current policy evidence.

A rejected permission cannot be turned into success by retrying without a cache. An allowed variation with a mismatching cached artifact normally needs a different artifact, not a policy waiver.

## 2. Gate ordering

```text
exact staged/committed/integration snapshot
                  |
resolve toolchain + configuration + effective policy
                  |
validate project predefinitions and provider registrations
                  |
classify strict / complex / none obligations
                  |
validate native graph/profile/policy stamps
                  |
lookup admissible resource/action evidence
                  |
execute missing or deliberately uncached actions
                  |
validate actual dependency/context observations
                  |
validate outputs + current attempt fence
                  |
affected unit / contract / layer / feature tests
                  |
complete receipt for this exact snapshot and policy
```

Entry-policy checks happen before an object-cache hit. File/context checks may require qualified prior dependency evidence or a fresh scan. A missing complete trace cannot become a successful negative proof. For an allowed full-context mode, conservatively key the complete immutable accessible input universe and invocation rather than making unsupported precision claims.

The gate also runs when the native build tool considers the target up to date. P11 showed that a compiler launcher is not invoked for an undeclared policy-only edit; P12 showed the additional object-dependency mechanism for the tested CMake/Ninja case. The production adapter therefore needs an always-run top-level gate and dependency-stamp integration. [Local evidence](evidence/probe_results.md) [S08](#s08) [S11](#s11)

## 3. Local and GitHub workflow

| Entry point | Required header-policy work | What it cannot claim |
|---|---|---|
| Pre-commit | Validate staged policy syntax/structure, rule conflicts, obvious target-definition drift, ownership and exception review fields. | A syntax-only or command-line-only check is not full preprocessing validation. |
| Explicit ready/pre-PR preflight | Resolve exact profile; semantic candidate compile; policy/resource validation; affected mandatory tests. | A 60-second cutoff does not authorize an incomplete pass. |
| Pre-push | Check outgoing committed revisions and whether matching required evidence exists; retain cheap integrity guards. | A working-tree fix does not validate a broken committed revision. |
| PR CI | Run the same semantics on an immutable candidate with the applicable protected policy; isolate untrusted work. | A PR cannot self-authorize arbitrary weakened exceptions. |
| Integration | Rebind evidence to the current base plus candidate; rerun newly affected actions. | Head-only evidence is not automatically evidence for a changed merge result. |
| Scheduled qualification | Clean-vs-cached, mutation, provider reset, resource-sharing, and race/failure tests. | A cache hit is not an independent clean rebuild. |
| Release | Supported toolchains/profiles and ABI domains; exact artifacts and dependency pins; clean qualification where required. | Relaxed developer profiles cannot silently become release policy. |

Preserve the earlier warm ordinary-change **P95 <60 seconds** objective. It is not a cold-build guarantee. Capture wall time including scanning, policy evaluation, tool acquisition, queueing and verification. Return `INCOMPLETE` with remaining action IDs at a feedback deadline; extended CI may finish the work, but only its completed evidence admits the change.

The proposed receipt adds `effective_policy_digest`, `macro_profile_digest`, registered-provider roots, exception IDs and versions, cache-mode decisions, native bridge status, context-completeness capability, and resource/result digests to the existing snapshot/toolchain/test fields. Record exact cache reuse versus actual execution. Exception approval time/expiry belongs to policy admission; it must be checked freshly, not frozen forever inside an old successful artifact.

Local hooks and a `gh` wrapper remain convenience entry points. Required remote admission must not rely on users always invoking them. Preserve the previous plan's staged/committed-snapshot handling, JJ/`sj` wrapper seam, fork-safe execution, protected policy verification and existing required checks. No GitHub rule or workflow has been changed by this report.

## 4. Dependency selection and compatibility

A macro that changes a declaration, template, inline body, constexpr result, pragma state, or include resolution is a **compile-semantic dependency**, not just an ordinary function-interface change. Select consumers from the old and new dependency snapshots; deletion of a macro/provider must not remove the evidence needed to invalidate prior consumers.

Policy scope changes also invalidate or re-admit governed resources. A rule change confined to one vendor subtree need not rebuild unrelated targets if the policy compiler can prove that confinement. Until then use a broader conservative policy root. Never trade soundness for a smaller rebuild graph.

Select tests independently from ordinary compilation avoidance:

| Test class | New coverage |
|---|---|
| Unit | Rule matching, macro identity, ordered argument parsing, state classification, canonical encoding. |
| Contract | C/FFI provider interface; SDN↔typed representation; resource evidence and admission; native output/depfile behavior. |
| Layer | Preprocessor/header cache, module/PCH service, CMake/Ninja adapter, scheduler/publication. |
| Feature | A real application built under declared profiles, approved vendor exception, no-cache source, changed generated header. |
| System | Concurrent mixed profiles, node failure, cold cache, remote cache trust boundaries, cross-compilation. |
| Release | Required public ABI/configuration domains and supported native runtime profiles. |

A legal per-TU variant is not necessarily legal across a shared public ABI or inline/template definition. Require explicit equality for registry-defined ABI/ODR domains and test those boundaries. This is a conservative contract for identified domains, not a claim to solve every C++ one-definition-rule violation automatically.

## 5. Repository, submodule, and branch policy

Keep shared compiler/runtime and dependency/cache contracts in the coupled monorepo. Put the generic policy evaluator and resource interfaces in reusable libraries, with separate Simple and Clang providers. Do not create long-lived Git branches for macro configurations, SDK versions or SIMD features; express those as profiles and exact toolchain identities.

Independent example applications can remain commit-pinned submodules or locked fetched dependencies. The parent may provide a reviewed sidecar header-policy registry so vendor source need not be edited. Bind those rules to dependency identity, version/commit and resolved input roots. A parent gitlink change invalidates both the input closure and the applicability of old vendor exceptions. An exception for one SDK revision must not automatically cover an unrelated replacement at the same path.

Keep one authoritative dependency pin: gitlink for a submodule, SDN lock entry for a fetched dependency. Generated files are producer outputs with graph edges, not material that a submodule checkout happens to leave behind. Native compiler/configuration probes use their explicitly scoped probe profile and cannot publish product artifacts into a release cache namespace.

## 6. Failure and retry decisions

| Situation | Classification | Required action |
|---|---|---|
| Unknown entry definition or illegal fixed value | Policy error | Stop that action; no uncached retry to evade the rule. |
| Scoped exception does not cover a strict consumer | Policy error | Show origin, escaping consumer and matching rules; fix scope or source. |
| Allowed macro variant differs from an old PCH | Cache mismatch | Select/build the correct native variant; do not reuse incompatible bytes. |
| Supported complex mode lacks a complete context | Unsupported/incomplete | Use only the rule's explicit `none` fallback or return an error/incomplete result. |
| Ordinary compiler diagnostic | Code failure | Preserve diagnostic; no pass-seeking retry. |
| Cache digest or evidence mismatch | Integrity failure | Quarantine the mapping; reconstruct from independently admitted inputs. |
| Group process crashes | Infrastructure/tool interruption | Fence the group; inventory all unfinished actions; discard suspect mutable state; bounded isolated retries. |
| Fresh isolated mode succeeds but grouped mode fails | Isolation-sensitive defect | Keep evidence; quarantine grouped qualification; use admitted isolated mode. |
| Worker disappears or preempts | Infrastructure interruption | Fence old publication; reschedule replay-safe work on a compatible worker. |
| Same complete key for a deterministic/cacheable action yields unequal outputs | Nondeterminism/key defect | Preserve both, quarantine reuse, and produce a reproducer. |
| No-cache source is hidden inside a cached parent | Policy violation | Reject parent reuse and schedule fresh required processing. |
| Native tool skipped a required fresh action | Adapter/admission failure | Force a supported dirty transition or reject delegation; do not emit a pass. |

Each retry retains the original macro environment, toolchain, policy and snapshot. Recovery may change the execution mode or machine within the admitted envelope; it may not silently remove definitions, replace a library, broaden an exception or switch off the verifier.

Use the previous plan's separate `ActionSpec`, `AttemptSpec` and validation identity. Publication uses current action/attempt/group epochs, complete payloads, and broker validation. A thread failure can corrupt the group, so do not replace one thread and reuse all group state as though each thread were a process. The cache/resource broker must not let an old failed attempt overwrite a later accepted result.

## 7. Implementation packages

These packages extend, rather than replace, the earlier W0–W10 build-platform program. Names and paths are proposed; reconcile final placement with the active repository before coding.

| Package | Owner / dependencies | Deliverable | Release gate |
|---|---|---|---|
| H0 — Policy/schema freeze | Architecture owner; existing W0 | Versioned SDN registry, profile inheritance, exact mode semantics, error catalogue and threat model. | Review confirms no exception means “omit from key”; all outcomes unambiguous. |
| H1 — Invocation and snapshot capture | Clang/native adapter owner; H0, W1 | Exact driver/response inputs, builtins/profile roots, generated/header search inputs; isolated reference execution. | Ordered and negative-dependency counterexamples are represented or conservatively covered. |
| H2 — Policy evaluator | Policy owner; H0–H1 | Cold/warm identical entry/file validation; origin+consumer matching; protected exceptions and expiry. | Planned policy tests pass with deliberate rejection fixtures. |
| H3 — Cache eligibility and evidence | Existing cache owners; H1–H2, W2–W4 | Typed completeness records, exact keys, policy admission, ancestor no-cache propagation, publication fences. | Clean/cached mutation suite has no known false hit. |
| H4 — CMake launcher and native bridge | Build adapter owner; H1–H3 | Launcher, top-level gate, effective-policy stamps, no-cache force-execution, side-output parity. | Policy-only, same-mtime, generated-input and native-no-op tests pass. |
| H5 — Native PCH/module resources | Clang owner; H3–H4, W3 | Controlled PCH/native module actions, correct option context, import/build evidence and bounded single-flight. | Matching/mismatching and nested-exception tests pass. |
| H6 — Qualified library/group provider | Clang/runtime owners; H3–H5, W5–W6 | Exact Clang C++ adapter behind a C ABI; private compile state; shared startup caches; isolated fallback. | Concurrent profile/reset/crash equivalence and measured benefit. |
| H7 — Optional fine-grained cache/Ninja work | Separate specialist owners; H3–H6 | Qualified full PP state replay or reduced dependency projection; complete Ninja features where justified. | Independent capability certification; unsupported constructs never silently ignored. |
| H8 — CI and configuration compatibility | CI/test owner; H2–H5, W7–W8 | Common receipts, unit/layer/feature selectors, explicit ABI domains, fork-safe policy handling. | Every submission path enforces current complete evidence. |
| H9 — Independent qualification | Verification owner; enabled H0–H8, W10 | Evidence package, performance data, release profile coverage and rollback drills. | No unqualified precision/concurrency mode required for release. |

Parallel work begins after H0: invocation capture, policy evaluation against synthetic records, and acceptance fixtures can proceed independently. Do not let the advanced threaded adapter delay a correct isolated launcher. Generalized header replay is not necessary to obtain useful PCH/module/action reuse.

## 8. Planned acceptance catalogue

The following **56 scenarios are requirements**, not executed implementation tests. P01–P12 are narrower native-language/build-tool counterexamples linked where relevant. Each acceptance scenario needs an implementation fixture, explicit expected result, owner and machine-readable receipt.

| ID | Area | Scenario | Required outcome | Related local probe |
|---|---|---|---|---|
| HC01 | Policy | Unexpected -D on a cold build | Policy error before artifact admission. | P01 |
| HC02 | Policy | Same forbidden invocation with a warm object/PCH cache | Same error; cached success cannot bypass policy. | — |
| HC03 | Policy | Fixed macro changed, removed, or defined-empty | Reject the exact forbidden definition state. | P01 |
| HC04 | Policy | Declared variant uses an admitted value | Accept permission; reuse only matching context or build a new variant. | — |
| HC05 | Policy | Declared variant uses an out-of-domain token spelling | Reject rather than silently adding a variant. | — |
| HC06 | Policy | -D/-U order or response-file content changes | Preserve semantics and revalidate/rekey; no sorting. | P03 |
| HC07 | Policy | Compiler builtin profile changes across approved targets | Select distinct approved toolchain/profile identities, not false project drift. | — |
| HC08 | Policy | Project attempts unauthorized builtin override | Reject or require the explicit narrowly reviewed override rule. | — |
| HC09 | Policy | Registered config provider emits an unapproved macro/value | Provider registration alone does not waive the violation. | — |
| HC10 | Policy | Exception origin matches but effect reaches a strict consumer | Reject scope escape unless separately authorized. | — |
| HC11 | Policy | Overlapping, conflicting, expired, or identity-mismatched rules | Deterministic error; no last-writer-wins admission. | — |
| HC12 | Policy | New source-internal define stays in a non-reusable local scope | Compile normally; do not require needless global feature registration. | — |
| HC13 | Preprocessing | An absent macro becomes defined for a previously ordinary identifier | Invalidate reduced evidence or retain complete environment identity. | P02 |
| HC14 | Preprocessing | undefined, 0, empty and 1 macro states | Distinct identities and correct native output. | P01 |
| HC15 | Preprocessing | Function-like macro stringification, token-pasting and rescanning | Preserve token spelling/spacing and newly consulted names. | — |
| HC16 | Preprocessing | Previously absent __has_include candidate appears | Invalidate absent-candidate witness; do not rely only on positive depfiles. | P04 |
| HC17 | Preprocessing | Same include spelling resolves after search-path reordering | Re-resolve and select changed input/context. | P05 |
| HC18 | Preprocessing | Higher-priority header, VFS overlay, symlink or case collision changes | Validate actual resolution and snapshot identities. | — |
| HC19 | Preprocessing | Repeated X-macro .inc under different function definitions | Reprocess each invocation or use a fully qualified transition. | P06 |
| HC20 | Preprocessing | Identical header entered under different pragma pack state | Separate complete state or no resource reuse. | P07 |
| HC21 | Preprocessing | Identical preprocessing context but preceding typedef/namespace differs | Do not treat a header PP key as an arbitrary AST key. | P08 |
| HC22 | Preprocessing | __COUNTER__ starts from different state | Preserve or reject unsupported replay; no stale counter output. | P09 |
| HC23 | Preprocessing | __FILE__, line directives, date/time or timestamp context changes | Track/normalize by explicit policy or execute uncached. | — |
| HC24 | Preprocessing | Include guards, pragma once, push_macro/pop_macro and outgoing definitions | Preserve the supported full transition or fall back explicitly. | — |
| HC25 | Cache | Native PCH matching and mismatching macro configurations | Matching permitted; mismatch rejected/rebuilt, never force-loaded. | P10 |
| HC26 | Cache | Policy changes while object bytes/key from prior policy exist | Fresh policy admission before hit; no stale waiver. | — |
| HC27 | Cache | Complex mode cannot supply all required context fields | Explicit none fallback or error; no fake completeness certificate. | — |
| HC28 | Cache | No-cache header nested in PCH, PCM, prefix and full TU result | Reject ancestor shortcuts and run fresh governed semantic action. | — |
| HC29 | Cache | No-cache confidentiality disallows raw source persistence too | Respect separate storage policy; no implicit raw CAS publication. | — |
| HC30 | Cache | Same file size/mtime with changed bytes | Content verification and native dirty bridge catch the change. | — |
| HC31 | Cache | Header changes between dependency capture and compilation | Snapshot restart or publication rejection. | — |
| HC32 | Cache | Partial, truncated or tampered context/resource manifest | Reject and quarantine; no claimed-digest-only trust. | — |
| HC33 | Cache | Many waiters request one variant; one waiter cancels | Single admitted producer; needed work continues. | — |
| HC34 | Cache | Variant/resource memory budget is exhausted | Evict safely or use approved fallback; never collapse distinct keys. | — |
| HC35 | Provider | Many concurrent compile requests with different macro profiles | Grouped output matches isolated reference; no cross-request leakage. | — |
| HC36 | Provider | Warm worker reuses thread-local state after prior failure | Reset validated or process discarded; diagnostics/private state isolated. | — |
| HC37 | Provider | Attempt to share one mutable Clang AST across compilations | Provider API/qualification rejects unsupported sharing. | — |
| HC38 | Provider | Group killed while multiple header and object actions run | All unfinished actions inventoried; stale publications fenced. | — |
| HC39 | Provider | Old attempt returns after replacement succeeds | Reject stale fence and preserve accepted result. | — |
| HC40 | Provider | Equal complete action/context keys produce unequal artifacts | Quarantine mapping/provider mode and retain reproducer. | — |
| HC41 | Native integration | CMake launcher invoked for a dirty native TU | Capture exact real command, outputs, deps and diagnostic behavior. | P11 |
| HC42 | Native integration | Policy-only edit with otherwise clean Ninja graph | Top gate plus policy dependency triggers validation/required action. | P11/P12 |
| HC43 | Native integration | No-cache target requested twice with unchanged source | Native adapter forces required fresh processing both times. | — |
| HC44 | Native integration | Generated configuration output not present on first build | Producer graph runs before scanning or compiling. | P11 |
| HC45 | Native integration | Native PCH reuse target has different flags/definitions | Reject sharing or produce a separate valid resource. | P10 |
| HC46 | Native integration | Compilation database lacks link/custom-command/dyndep actions | Do not claim a full build; retain complete native graph execution. | — |
| HC47 | Native integration | Ninja importer sees unsupported grammar/graph feature | Delegate whole safe boundary or fail unsupported; no dropped edges. | — |
| HC48 | Native integration | Compiler source writes split debug/module/depfile side outputs | Capture and materialize all required outputs atomically. | — |
| HC49 | CI/repository | Staged/committed/integration snapshots differ from working tree | Gate the intended snapshot and policy, not convenient local bytes. | — |
| HC50 | CI/repository | PR weakens registry or forges an old successful receipt | Protected policy/issuer/current-input validation prevents self-admission. | — |
| HC51 | CI/repository | Fast lane deadline expires with mandatory work pending | INCOMPLETE with remaining IDs; no truncated PASS. | — |
| HC52 | CI/repository | Vendor submodule pin changes under an existing exception | Revalidate identity, scope and current actual inputs. | — |
| HC53 | CI/repository | Public ABI macro differs across governed linked targets | Compatibility gate rejects mismatch independently of cache validity. | — |
| HC54 | CI/repository | Header inline/template/body changes but ordinary interface hash stays equal | Compile-semantic consumers and relevant behavior tests invalidate. | — |
| HC55 | CI/repository | Direct bare Ninja/gh or alternate client bypasses local wrapper | No complete admission without current trusted remote evidence. | — |
| HC56 | CI/repository | Grouped optimized mode is disabled during rollback | Permission checks and correctness gates remain enforced. | — |


## 9. Benchmark design

Use a pinned real-world header-heavy C++ corpus and a controlled synthetic corpus. Compare fresh processes, warm singleplex processes, qualified groups, and groups with native header resources. Measure dynamic versus static Clang linkage at the same process lifetime; otherwise startup and linkage changes are confounded.

Measure policy scan CPU, macro-state fingerprint cost, full-context versus qualified precision, raw/PCH/PCM/object hit rates, replay/deserialization, bytes read/transferred, private/shared memory, variant cardinality, lock wait, queue time and tail latency. Include policy-only edits, newly created headers, heavily shared generated configuration, X-macro fragments and deliberate no-cache targets. Count how many native compilations actually ran.

No fixed speedup is claimed. An optimization is admitted only after correctness parity and a useful measured improvement for its target workloads. If full-context keys are too costly, optimize their construction and persistence before deleting inputs. If a dynamic library provider is slower than a static warm process, retain the common interface and choose the faster qualified configuration.

## 10. Rollout and rollback

Start in an observation-only developer lane that emits proposed profiles and violations, clearly labeled non-admitting. Review the baseline rather than automatically enrolling every observed definition. Onboard first-party roots and known SDK profiles into strict enforcement, then add narrow vendor exceptions with owners. A new exception remains a reviewed policy change, not an automatic fix suggested and applied by the cache.

Progress through isolated complete-context correctness, native launcher integration, PCH/module sharing, and only then grouped execution or precision optimizations. Run the optimized and reference paths in shadow comparison on a representative subset and periodically run clean full cases.

Rollback switches are independent: full context instead of reduced context; no header resource instead of token replay; isolated process instead of threaded group; native Ninja instead of an incomplete importer. **None of these may disable strict permission checks.** A policy may explicitly permit no-cache fallback, but a global “ignore all macros” emergency flag is not an admitted release mode.

The completion package contains frozen schemas, actual toolchain digests, policy decisions, executed acceptance receipts, trace/corruption/crash fixtures, benchmark methodology/results, and supported-platform limits. Documentation and successful counterexample probes alone do not constitute production qualification.


---

<a id="report-5"></a>

# Report 5 — Sources, executed probes, and evidence limits

**Research date:** 2026-09-25  
**Source policy:** Primary project documentation and upstream source. No repository or GitHub settings were modified. This extension is not a fresh source audit of `ormastes/simple`.

## Evidence categories

**Design proposal.** The strict registry, exception semantics, completeness contracts, Simple C ABI/provider, launcher subcommands, and CI gates are proposed by these reports. They are not claimed to exist in an installed Simple release.

**Upstream facts.** The references below establish available Clang/CMake/Ninja mechanisms and documented limitations. Online `latest` and LLVM `main` pages may describe development versions. Use the exact headers/options of the implementation's pinned toolchain; do not infer that Clang 17 has every API appearing in current Doxygen.

**Local execution.** Twelve small native counterexample probes were executed using the tools recorded below. These validate selected language/build-tool behaviors, not the soundness, performance, or completeness of the proposed cache.

**Prior session plan.** The supplied four-report build-platform plan is copied unchanged into [prior_plan](prior_plan/README.md). Its existing repository findings belong to its stated historical audit commit, `ed75897fe050d874ce7c7bcd90c2b30953ad65ce`; they were not re-established against a newer tree in this extension.

## S01

[Clang: Modules](https://clang.llvm.org/docs/Modules.html)

Relevant sections: configuration macros, module variants, textual headers and context options. The document describes `config_macros` and its limited warning behavior, and says the `exhaustive` variant-reduction optimization is not implemented. This is not the proposed project-wide strict allowlist. `-fmodules-ignore-macro` is not a substitute for an approved varying-macro policy.

## S02

[Clang: Precompiled Header and Modules Internals](https://clang.llvm.org/docs/PCHInternals.html)

Establishes native serialization and lazy loading of compiler state. Used to distinguish a native serialized prefix/module resource from a string of preprocessed tokens or a pointer to a live AST. It does not certify arbitrary fragment replay by an external cache.

## S03

[Clang Doxygen: PPCallbacks](https://clang.llvm.org/doxygen/classclang_1_1PPCallbacks.html)

Establishes the available observation family for preprocessing. The retrieved Doxygen describes a development toolchain, not the locally tested compiler. API presence alone does not prove a complete negative macro/file dependency set; additional instrumentation or conservative full-context identity remains necessary.

## S04

[LLVM upstream: clang/tools/clang-shlib/CMakeLists.txt](https://github.com/llvm/llvm-project/blob/main/clang/tools/clang-shlib/CMakeLists.txt)

The inspected upstream file defines a `clang-cpp` shared-library target and its build constraints. The `main` URL is a moving reference; production must pin a commit and verify its platform-specific targets. This report did not build that library.

## S05

[Clang: Choosing the Right Interface for Your Application](https://clang.llvm.org/docs/Tooling.html)

Distinguishes the deliberately stable, limited libclang C surface from the richer C++ tooling interfaces and their evolution. Supports placing an exact-version adapter behind Simple's own controlled C ABI; it does not promise compatibility between arbitrary Clang builds.

## S06

[clangd: Threads and request handling](https://clangd.llvm.org/design/threads)

Documents thread-safe immutable preamble bytes and non-thread-safe live ASTs. This is evidence for the serialized-resource/private-context boundary, not proof that all Clang frontend actions are automatically safe to multiplex.

## S07

[LLVM: Building a Distribution of LLVM](https://llvm.org/docs/BuildingADistribution.html)

Relevant to consolidated versus per-component shared libraries, supported LLVM-dylib packaging, and performance/distribution tradeoffs. The documented LLVM-dylib mechanism excludes Windows; the report's Linux build template must not be treated as a verified Windows recipe. Neither the static nor dynamic provider template was executed here.

## S08

[CMake: `<LANG>_COMPILER_LAUNCHER`](https://cmake.org/cmake/help/latest/prop_tgt/LANG_COMPILER_LAUNCHER.html)

Establishes compiler-launcher integration for supported Makefile/Ninja generation. A launcher wraps an actual compiler invocation; it is not an always-run build-policy hook. P11 demonstrates the distinction locally.

## S09

[CMake: File API](https://cmake.org/cmake/help/latest/manual/cmake-file-api.7.html)

Establishes the versioned codemodel and related target/configuration/compiler metadata. The plan uses it for semantic ownership and configuration mapping, not as a replacement for every native build command or dynamic dependency. Actual invocations/native graph execution remain authoritative until a complete execution adapter exists.

## S10

[CMake: `target_precompile_headers`](https://cmake.org/cmake/help/latest/command/target_precompile_headers.html)

Documents native PCH creation, `REUSE_FROM` matching requirements, and controls to disable PCH use. Supports explicit compatible prefix resources rather than automatically combining unrelated targets' headers.

## S11

[CMake: `OBJECT_DEPENDS`](https://cmake.org/cmake/help/latest/prop_sf/OBJECT_DEPENDS.html)

Documents additional object prerequisites for supported Makefile/Ninja generators, not Visual Studio/Xcode. P12 exercises one practical policy-dependency mechanism. It is a building block, not the whole content-addressed or no-cache execution contract.

## S12

[CMake: `CMAKE_EXPORT_COMPILE_COMMANDS`](https://cmake.org/cmake/help/latest/variable/CMAKE_EXPORT_COMPILE_COMMANDS.html)

[Clang: JSON Compilation Database Format Specification](https://clang.llvm.org/docs/JSONCompilationDatabase.html)

Documents exported translation-unit invocations and their representation. Use the current CMake documentation for generator support. A compilation database is useful for TU discovery but is not a complete build, link, generator or test graph.

## S13

[Clang: Standard C++ Modules](https://clang.llvm.org/docs/StandardCPlusPlusModules.html)

Documents the standard-module compilation/dependency workflow. Supports keeping this provider kind separate from header modules and PCH. Named-module support must be qualified for each pinned Clang/CMake version rather than inferred from generic PCM terminology.

## S14

[GCC preprocessor manual: Standard Predefined Macros](https://gcc.gnu.org/onlinedocs/cpp/Standard-Predefined-Macros.html)

Primary compiler documentation used as a reference for context-sensitive standard builtins such as file, line, date and time. It is not evidence that every GCC-specific extension behaves identically in Clang. Clang-specific counter/state behavior in this report is supported separately by P09.

## S15

[Ninja: Manual](https://ninja-build.org/manual.html)

Documents the native graph/execution model, dependency categories, variable and file scopes, pools, response files, generator behavior and dynamic dependencies. Used to define the completeness obligation for an optional Ninja adapter, rather than suggesting a line-oriented importer is sufficient.

## Executed local environment

| Tool | Actual local version |
|---|---|
| Clang | 17.0.0, Swift LLVM build `10999b6d034fe318f3d56c83bddb6572593a8bb0` |
| Clang target | `x86_64-unknown-linux-gnu` |
| CMake | 3.31.6 |
| Ninja | 1.12.1 |

These are the available test tools, **not a recommendation to pin the implementation to Clang 17**, nor a statement of the newest available versions. No cross-platform or shared-library build qualification was performed.

## Executed probe outcomes

All **12/12** counterexample probe groups passed their explicit expected outcomes. Some PASS results deliberately demonstrate a limitation—for example, P11 passes when the undeclared policy change does not invoke the launcher.

| Probe | Observation |
|---|---|
| P01 | Undefined, zero, empty and one definitions differ. |
| P02 | A previously unexpanded identifier can become a macro dependency. |
| P03 | Ordered `-D/-U` operations change preprocessing. |
| P04 | A newly present optional include changes output despite its prior absence from an ordinary depfile. |
| P05 | Include-search ordering can select different header contents. |
| P06 | One X-macro fragment is intentionally expanded twice under different definitions. |
| P07 | Entering packing state changes layout for the same header on the tested ABI. |
| P08 | A preceding typedef changes the meaning of an otherwise identical header. |
| P09 | `__COUNTER__` depends on entering state. |
| P10 | Native Clang rejects the tested incompatible PCH macro configuration. |
| P11 | CMake launcher/File API integration works; an undeclared policy-only edit is skipped by Ninja. |
| P12 | Adding the policy file as an object prerequisite triggers compilation in that case. |

Full observed outcomes are in [probe_results.md](evidence/probe_results.md), commands/outputs in [probe_results.json](evidence/probe_results.json), and all fixture construction in [run_probes.py](evidence/run_probes.py). The script creates a temporary work directory and removes compiled outputs after the run. It can be rerun with Python 3 and the required native tools on PATH; fixed layout assertions are specific to the tested x86_64 ABI.

The 56 HC acceptance scenarios in Report 4 are **not** counted as executed. They require a future implementation. The bundled SDN is an authoring example, not parser-validated configuration. The policy text in P11/P12 was intentionally opaque to the logging launcher; those probes do not implement macro enforcement.

## What remains unproven

No measured throughput improvement, sub-minute CI performance, end-to-end cache soundness, Clang C++ ABI compatibility, compiler-group reentrancy, complete preprocessor replay, SDN parser compatibility, distributed failure recovery, or repository integration is claimed. The design explicitly retains conservative/isolated reference paths until those properties are qualified.


---

<a id="local-probes"></a>

# Local counterexample probe results

Counterexample probes only; no Simple cache/provider implementation was tested.

Executed in this conversation on 2026-09-25. This is not a performance benchmark or a cache soundness proof.

## Toolchain

### clang
```text
clang version 17.0.0 (https://github.com/swiftlang/llvm-project.git 10999b6d034fe318f3d56c83bddb6572593a8bb0)
Target: x86_64-unknown-linux-gnu
Thread model: posix
InstalledDir: /usr/local/swift/usr/bin
```

### cmake
```text
cmake version 3.31.6

CMake suite maintained and supported by Kitware (kitware.com/cmake).
```

### ninja
```text
1.12.1
```

## Results

| ID | Probe | Outcome | Observation |
|---|---|---|---|
| P01 | Macro definition states are distinct | PASS | Undefined, defined-as-0, defined-empty, and -DMODE (1) produced four distinct results. |
| P02 | Previously unexpanded identifier changes | PASS | An ordinary identifier with no original expansion becomes a macro use after a new definition. |
| P03 | Ordered command-line macro actions | PASS | Reversing -D/-U changed preprocessing; argv ordering cannot be sorted away. |
| P04 | Negative include dependency | PASS | An absent header did not appear in the ordinary dependency list; creating it changed output. |
| P05 | Include-search order is semantic | PASS | The same include spelling selected different content when include search order changed. |
| P06 | Repeated X-macro include | PASS | One header was intentionally processed twice under different function-like macro definitions. |
| P07 | Non-macro pragma state changes layout | PASS | On this x86_64 toolchain, identical header bytes yielded size 8 or 5 under different pragma state. |
| P08 | Textual header semantic context | PASS | The unchanged header and macro configuration still depended on a preceding typedef; header AST reuse needs semantic context. |
| P09 | Stateful builtin counter | PASS | __COUNTER__ reflected incoming preprocessing state, not just macro replacement text. |
| P10 | Native PCH mismatch validation | PASS | Clang accepted matching PCH macro settings and rejected MODE=2 against a MODE=1 PCH. |
| P11 | CMake launcher integration and policy skip hole | PASS | Launcher and File API worked; Ninja did not invoke the launcher on an unchanged build or an undeclared policy-only edit. |
| P12 | Explicit policy dependency closes launcher skip hole | PASS | Adding the registry with OBJECT_DEPENDS made the policy edit trigger another compilation through the launcher. |

## Reproduce

Run `python3 evidence/run_probes.py` with clang, CMake, and Ninja on PATH. The script uses a temporary directory, removes generated binaries, and writes its own results beside itself. The fixed layout checks are specific to the observed x86_64 ABI.

The machine-readable log is `probe_results.json`; full fixture source is in `run_probes.py`. The policy file in the launcher fixture is intentionally opaque text, not a validation of the proposed SDN schema.
