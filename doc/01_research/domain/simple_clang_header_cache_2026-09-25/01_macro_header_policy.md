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

Clang module maps provide `config_macros`; their documented implementation uses a limited check for configuration changes, and the `exhaustive` optimization is not implemented as a general verifier. Therefore the project-wide strict allowlist is a Simple policy layer, not a promise that adding one Clang flag implements this design. [S01](05_sources_and_evidence.md#s01)

Do not map exceptions to `-fmodules-ignore-macro`. That flag is intended for macros that do not influence the module; allowing a macro to vary is a different statement. Preserve ordinary compiler validation and reject cache-weakening flags that conflict with the policy.

## 12. Acceptance rule

An admitted cache hit requires all of: permitted variation, complete matching inputs/context, supported resource boundary, verified bytes/manifest, valid producer provenance, and current policy evidence. Failure of any condition cannot become a successful strict hit.

The policy evaluator must be deterministic between cold/warm caches, local/remote workers, and grouped/isolated execution. Performance changes implementation cost, not the contract.
