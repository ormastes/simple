> Update 2026-11-03: the XRay runtime/lifecycle portions are superseded by [the staged XRay design](simple_xray_staged_implementation_plan_2026-11-03.md). Visibility, grammar and tooling requirements remain applicable. See [integration status](xray_v1_integration_status_2026-11-03.md).

# Simple: Aspect Dynload and Visibility Improvement Plan

**Date:** 2026-10-31
**Revision:** 1.1 — supplied plan preserved; Astra release-branch reconciliation added 2026-11-01
**Status:** Design selected; historical audits preserved; initial implementation slices in progress and unverified; feature acceptance remains open
**Repository:** `ormastes/simple`
**Historical audited branch / commit:** `main` / `97700b29e10675867891503f1e634b50a192356d`
**Reconciliation target / base:** `release/1.0.0` / `d9ff974b3c967579ab00b64ef7d03ae2424d8e4e` (local checkout reviewed 2026-11-01)
**Scope:** Pure-Simple compiler/runtime integration, AOP grammar, directory visibility, LSP/MCP visibility views, and development/release bootstrap policy.

**Current goal precedence (2026-11-02):** The renewed user goal additionally
requires generated getters/setters, implicit accessor generation for aspect
get/set, and generated pointer-traversal plugins with caching. Those requirements
supersede this historical plan's accessor exclusions and cannot be deferred out
of completion. The [current requirements](../../../02_requirements/feature/aspect_dynload_visibility.md)
and [pending implementation choices](../../../02_requirements/feature/aspect_generated_accessors_pointer_traversal_options.md)
record that extension. The original exclusions below remain as historical design
context; they do not authorize declaring the renewed goal complete without these
features. No implementation or acceptance pass for them is claimed.

**Implementation tracking:** [lane ownership](../../agent_tasks/aspect_dynload_visibility.md)
and [acceptance execution](../../sys_test/aspect_dynload_visibility.md). The
read-only audit statements below describe their dated inspections, not later
implementation activity. External host XRay probe success does not establish
Simple integration or satisfy the native feature matrix.

The [recovery acceptance ledger](../../../09_report/compiler/aspect_dynload/recovery_acceptance_2026-11-01.md)
records the subsequent build failures, bounded native evidence, and still-open
implementation gates. Source-review passes do not constitute feature acceptance.

<!-- codex-research -->
<!-- codex-design -->

## 1. Executive decision

Implement a small, explicit extension to the existing system:

1. Connect the existing aspect-pack loading infrastructure to **LLVM XRay execution instrumentation** for dynamically enabled observational aspects.
2. Fix AOP parsing, selector validation, `within`/`attr` matching, and named-aspect ownership. Do not introduce a new general-purpose weaving language.
3. Move execution-between-folders logging into a **dynloadable debug aspect**, with thread-local tracking and compile-time directory identities. Development builds enable this debug option; release builds compile it out.
4. Build **phase 3 with a development profile** and **phase 4 with a release profile**, consistently across commands, managed-job receipts, caches, and publication.
5. Make the compiler, TLDR metadata, AOP selection, LSP, and MCP share one visibility model. The current implementation and visibility view are present but inconsistent with the requested semantics.

The document covers the whole session, but later scope restrictions take precedence over earlier possibilities. In particular, this change does **not** implement `call`, generated getters/setters, typed parameter/return matching, argument/return capture, dynamic `around`, or a second runtime weaving engine.

“Folder move” means **execution moving between functions owned by different source folders/layers**. It does not mean monitoring filesystem renames, `chdir`, or file writes.

### 1.1 Final visibility terminology

| Term | Meaning in this plan |
|---|---|
| No `pub`/`pri` modifier | Folder-local for top-level declarations: accessible from files in the same immediate logical source directory, not automatically from children, siblings of that directory, or its parent. |
| `pri` | Explicitly private. Preserve declaring-scope privacy; for top-level declarations this is file-private. Do not silently change member/type privacy. |
| `pub`; feature-public | The ordinary public declaration surface: **all `pub` declarations**, not a new feature-package access modifier. Public members still depend on accessibility of their containing type. |
| Layer-public | An exported binding in a directory's resolved `__init__.spl` interface. It is relative to that directory boundary and can expose a selected otherwise-folder-local declaration. |
| Reachable from requester | Whether a particular reference is legal from a particular source location, through a particular module/export route. This is separate from the two public-surface classifications. |

`pub` does not override a closed ancestor directory. “All public” classifies declarations; legal access still needs an accessible module/export route. This preserves directory encapsulation and corrects the earlier conversational suggestion that feature-public could bypass every parent boundary.

Layer-public and feature-public are **overlapping classifications, not three new access keywords**. A folder-local function may be layer-public through an explicit façade export without becoming a `pub` declaration. Conversely, a `pub` function can be feature-public without appearing in a particular layer interface.

### 1.2 Development and release contract

| Artifact/profile | XRay boundary candidates | Folder-trace aspect | Recording default | Runtime debug activation |
|---|---|---|---|---|
| Phase 3, development, supported target | Compiled in | Loadable; activated by the development debug option | Enabled for folder transitions; depth included on transition records | Allowed; explicit opt-out disables recording/patches |
| Development with folder tracing explicitly disabled | Still available if built XRay-ready | May remain unloaded or disabled | Off | Can be enabled later |
| Phase 4, release | Not emitted | Not bundled or auto-loaded as a debug dependency | Off | Rejected/unavailable; environment variables cannot turn it on |
| Development, unsupported backend/target | Not available | Not activated | Unavailable, with an explicit reason | An explicit request fails clearly; never silently substitutes another engine |

Development **enables the debug option**, not merely the possibility of using it. An opt-out remains necessary for measurements and noisy workloads. Unsupported capability is not reported as a successful trace test. Normal functional component loading and `DynLib` use remain available in release; only this optional debug-aspect path is gated.

## 2. Audit basis and confidence

The following audit account and R/E references preserve the supplied 2026-10-31 main-branch history. They are not a fresh remote-head or external-document verification. Section 2.3 records the separate 2026-11-01 local release-branch reconciliation and takes precedence for implementation on that branch.

The public remote `HEAD` was checked and matched the audited commit above. `release/1.0.0` had a different head, `950fe6865d3d667491b294c17c6212424ef2262b`; that branch is **not** covered by this source audit.

This is a read-only inspection of owned source and selected existing tests/designs. No implementation patch, bootstrap build, runtime benchmark, or executable LSP acceptance run was performed. Finding a test file, an activation enum, or a documentation claim does not prove end-to-end functionality.

Repository research/design guidance informed the source-to-test mapping. The checked-out common SPipe submodule was not populated, and the repository knowledge registry has no exact route for this combined feature. The available compiler/runtime/tooling layer guidance was inspected. Register the exact feature route and knowledge receipt before an implementation lane; these setup gaps do not prevent this standalone plan.

### 2.1 What actually exists

| Area | Audited behavior | Consequence |
|---|---|---|
| Native startup aspect loading | `runtime_native.c` opens shared libraries and calls `simple_aspect_pack_init`; successful loads are retained. | Reuse the entry seam. It is not yet XRay pointcut routing or a safe hot-unload service. [R01] |
| Aspect-pack catalog | SMF catalog, byte loading, activation metadata, pinning, quiescing, and unload logic exist. | Extend these owners; do not replace them or repeat older claims that all catalog infrastructure is missing. [R02] |
| XRay bridge | No XRay emission/registration bridge was found in the inspected owned compiler/runtime/app/bootstrap paths. SimpleOS compiler-rt configuration explicitly disables XRay. | A real backend/runtime integration and target capability gate are required. [R03] |
| AOP validation | Selector extraction requires `(` immediately after the name, while the source parser serializes tokens with spaces. | Whitespace can bypass selector validation. [R04] |
| AOP matching | The token evaluator treats `call` like execution name matching, but makes `within`/`attr` return false. The validator advertises a different supported set. | Unify parsing and matching. Do not call this a working `call` implementation. [R05] |
| AOP ownership/ABI | Module-level `on pc` is parsed; the advice record lacks an aspect owner. MIR advice calls have no parameters and return unit. | Add ownership without changing advice signatures. [R06] |
| Existing debug logger | Depth, group stack, and entries are process-global; activation reads `SIMPLE_AOP_DEBUG`. | Do not reuse this state as thread-local or let it remain a second folder-trace engine. [R07] |
| Default visibility | Top-level parser and Tree-sitter outline collapse omitted visibility and explicit `pri` into private. | Preserve declaration intent. [R08] |
| Folder sharing | HIR already has directory-sibling namespace sharing. | Reuse its directory index; the problem is inconsistent enforcement, not total absence of folder access. [R09] |
| Visibility propagation | Some declaration/import paths use `Visibility.Public` unconditionally; production checking uses a binary public/private path despite richer scoped helpers. | Preserve and enforce the same semantic facts through every lowering/import path. [R09], [R10] |
| Auto-public and exports | Filename-based auto-public cannot reliably distinguish explicit `pri`; current export helper requires declaration-public, public child module, and export-list membership together. | Fix explicit-private handling and implement the requested explicit façade promotion rule. [R11] |
| LSP/MCP view | Hover, completion, tokens, and requester-aware visibility queries exist. `featurePublic` currently describes MDSOC capsule exports, not all `pub` declarations. | Version the semantics and preserve the legacy capsule concept separately. [R12], [R13] |
| Live editing and performance | Inspected `didChange` handler is a no-op; hot query routes launch subprocesses and use textual/name-based classification. | Unsaved-buffer correctness and fast canonical visibility views are not established. [R13] |
| Bootstrap policy | Both managed phase variants are constructed as release. CLI optimization can imply release mode. | Profile must be explicit and independent of optimization. [R14], [R15] |
| Cache/formal model | AOP keys currently normalize opaque predicate text; the Lean visibility model is binary public/private. | Version the pointcut/visibility contracts and test refinement against actual compiler behavior. [R16], [R17] |

### 2.2 Earlier statements this plan corrects

- Existing directory-sibling lookup is not equivalent to correct folder-local access control.
- Existing `layerPublic`/`featurePublic` output is not proof that those labels match the requested semantics.
- `HOT`/`LAZY_PATCHABLE` activation constants do not prove runtime XRay patching.
- Loading an aspect library is not the same as enabling its pointcuts.
- XRay hooks a surviving function execution, not each source call site or each re-export alias.
- The supported Boolean pointcut spellings are `&`, `|`, and `!`, not the earlier illustrative `&&` form.
- Depth changes occur on every observed entry/exit; printing every depth change is not a low-volume logging optimization.
- An XRay-ready but disabled build has sleds, metadata, and possibly boundary-preservation costs. It is not identical to a statically-off release build.

### 2.3 Astra reconciliation — 2026-11-01, release/1.0.0

**Review basis:** bounded inspection of owned source at local base `d9ff974b3c967579ab00b64ef7d03ae2424d8e4e`, in the isolated `work/aspect-completion-20261101` checkout. No remote-head check, external-document refresh, compiler invocation, executable test, capability probe, or benchmark was performed for revision 1.1. The historical main audit remains intact; its line numbers must not be used as current release-branch anchors. No item below is an implementation PASS.

The selected scope is unchanged: **getter/setter generation remains deferred**, as do `call`, value capture, and runtime `around`. These later restrictions supersede earlier conversational possibilities.

| Release-branch evidence | Reconciliation / actionable dependency |
|---|---|
| `runtime_native.c:19800–19945` loads both `SIMPLE_STARTUP_ASPECTS` and `--startup-extension`; `simple_startup_load_aspect_pack` calls `dlopen(..., RTLD_NOW \| RTLD_GLOBAL)`/`LoadLibrary`, invokes `simple_aspect_pack_init`, and returns without exposing a retained handle to the catalog. [Q01] | Residency is present, but this native path is not an unloadable catalog binding. Add explicit handle/generation ownership and failure cleanup to the existing loader boundary before offering replacement/unload. Include both argv spellings and environment activation in profile enforcement. |
| `llvm_native_link_hosted_support.spl:173–181` still calls the startup hook before runtime initialization. [Q02] | Defer the **load itself**, including native constructors, for Simple-dependent debug packs until runtime/TLS readiness. Moving only `simple_aspect_pack_init` is insufficient. Preserve the strong runtime-reference linkage described in Q01 so a weak startup hook cannot disappear from a static archive. |
| `aspect_pack.spl:2564–2579` explicitly says its basic lifecycle owns payload bytes, not executable mappings; V2 final-unpin reservation/commit APIs are also present. [Q03] | Reuse catalog state and V2 ownership, but add/verify physical executable release and protected callback acquisition. Do not infer native concurrency safety or successful `dlclose` from byte-catalog pins. |
| `aop_predicate_parser.spl:45–87`, `bitfield_aop_arch_decls.spl:188–222`, `aop.spl:382–399`, and `parser_types.spl:638–644` retain the whitespace-validation gap, execution-like `call`, false `within`/`attr`, and ownerless advice. [Q04], [Q05], [Q06], [Q07] | W2 is still required. Parser-only validation repair cannot establish matcher parity; retain one query representation, explicit aspect identity, and unsupported-selector rejection end to end. |
| The flat parser's current `parse_top_level_visibility` is at `enum_module_body.spl:617–642`, not the historical R08 range; it returns `private` for both omitted and explicit `pri`. Tree-sitter has the same collapse at `outline_decls.spl:119–140`. [Q08], [Q09] | Carry omission intent through flat AST storage, AST bridges, and serialization as well as the rich enum. A new enum variant alone cannot recover information already discarded by this parser. |
| `context_helpers.spl:246–253` first promotes ambient bootstrap declarations to `Public`; `module_declarations_bootstrap.spl:159` and several import-registration paths also substitute `Public`. [Q10], [Q11], [Q12] | Enumerate and test bootstrap/import bypasses before enabling enforcement. Filename matching and ambient bootstrap must not erase explicit privacy. The source migration needs real compiler/library fixtures; do not treat a UI label fix as V01 completion. |
| `dependency/visibility.spl:302–339` still requires declaration-public, public child module, and export membership together. `feature_visibility.spl:1–14` still defines capsule membership. [Q13], [Q14] | Implement binding-level façade promotion and requester access before reusing export data for XRay selection or changing query labels. Preserve capsule data under its own versioned field. |
| `lsp_handlers.spl:143–144` remains a no-op for changes. Query calls now route through `lsp_query_command.spl:25–32`, which uses bounded process execution. [Q15], [Q16] | A bounded subprocess is an existing transport improvement, not an in-process semantic cache. W7 still needs versioned overlays, a resident snapshot provider, and manifest dependency invalidation. Do not add a second shell-out path. |
| Both phase authority constructors still select `release` for phase 3. `native_group_index_variant.spl:31–42` couples release to optimization, and **both** CLI parsing (`compile_targets.spl:1023`) and central normalization (`driver_compile_options.spl:161`) infer release from optimization. [Q17], [Q18], [Q19], [Q20], [Q21] | Fix requested profile ownership and central normalization first; changing only shell flags or the phase constructor would be undone later. Keep artifact profile, optimization level, and resolved instrumentation capability distinct through command, receipt, variant, and final artifact. |
| `aop_group_keys.spl:1–16,217–222` explicitly documents textual selector hashing and a pre-weave-key input with no producer. `incremental.spl:747` builds a scope from lane/backend/CPU/features/optimization and compiler/provider/optimizer/guard identities. [Q22], [Q23] | W3 must connect actual producers/consumers, version the keys, and extend object/link identity with the normalized profile and instrumentation contract. Existing key types and sentinels are not working per-target weave artifacts or proof of C01/C02. |

No XRay bridge was found in the specific runtime, hosted-link, aspect catalog/I/O, AOP, and option-owner files inspected for this reconciliation. This is a bounded finding, not a whole-repository absence proof or a target capability result. The first admitted target remains unverified.

**Dependency order for release implementation:** freeze the declaration/export/selector and profile schemas (W0); establish profile permission before pack loading and correct central option normalization (early W6); preserve visibility intent and produce semantic/export indexes (W1–W3); admit one real native XRay route and protected executable ownership (W4); then attach bounded logging (W5), finish phase propagation (W6), and wire the resident tooling provider (W7). W7 can develop against the shared snapshot contract while native work proceeds. Default activation waits for the integrated acceptance gate (W8). Initial repair slices (for example selector validation, profile normalization, or visibility-intent storage) are prerequisites only: landing one or several does not complete W1–W8, establish native XRay support, or satisfy the feature acceptance matrix. Each implementation lane must report its actual completed subset and remaining gates.

**Unresolved implementation decisions:** select the concrete admitted hosted LLVM/runtime combination and prove its patch/unpatch semantics; choose and test the resident protected-reader protocol and executable-handle owner; identify every final object/link cache consumer; define pre-load classification of supported debug packs separately from functional startup extensions; and select measured performance baselines. These are explicit W0/W4/W6 deliverables, not silent assumptions or requests to expand scope.

## 3. Requirements and explicit exclusions

| ID | Requirement | Acceptance focus |
|---|---|---|
| A01 | Dynamically load/enable/disable an execution-observer aspect through the existing loader family and XRay. | Real instrumented binary plus pack lifecycle tests. |
| A02 | One token-aware pointcut parser, consistent matching, named-aspect ownership. | Parser/matcher/compiler/interpreter/LSP parity. |
| A03 | Keep advice parameterless and unit-returning; do not add value capture. | Signature rejection and unchanged application ABI. |
| V01 | Distinguish omitted visibility from explicit `pri`; implement same-folder default. | Compiler access matrix and Tree-sitter parity. |
| V02 | Resolve layer export bindings separately from all-public declaration classification. | Alias, ancestor, private-export, and multiple-boundary tests. |
| T01 | Thread-local observed folder/layer transitions using precomputed IDs. | Multithreaded nesting and known trace sequences. |
| T02 | Bounded logging, truthful observed depth, safe gaps/resets. | Overflow, mid-stack activation, unwind, task-switch cases. |
| B01 | Phase 3 development enables the folder-trace debug option; phase 4 release is statically off. | Command/receipt/artifact agreement. |
| B02 | Release cannot activate this debug path; ordinary dynload is preserved. | Negative activation tests plus functional-loader regression tests. |
| L01 | LSP/MCP show declared visibility, boundary exports, and requester reachability correctly. | Differential results against compiler access decisions. |
| L02 | Unsaved source and `__init__.spl` edits update views without per-request whole-tree scans. | Versioned overlays, invalidation, warm latency/RSS tests. |
| C01 | TLDR, reverse references, and object caches reflect semantic/profile changes without needless churn. | Invalidation and profile-isolation tests. |

Not in this implementation:

- `call` join points or caller-site weaving.
- Automatic hidden getter/setter generation, field pointcuts, structural introductions, or new object layout changes. Earlier getter/setter ideas remain deferred.
- Parameter/return-type discrimination or argument/return-value capture; concrete signature patterns must not be silently presented as implemented matching.
- Runtime `around`, runtime business-flow replacement, semantic error-result interception, or generic runtime weaving beyond XRay.
- A new feature-capsule language, a new GPU tracing backend, Cranelift emulation of XRay, or filesystem watchers.
- Exact full-stack depth or task/fiber-local call correlation. This version is thread-local and boundary-observational.

## 4. Canonical visibility and export semantics

### 4.1 Keep three facts separate

Store declaration intent, export surface, and requester access independently:

| Fact | Representative content | Changes when |
|---|---|---|
| Declaration | `DefaultFolder`, `Private`, `Public`, or an existing scoped modifier; owner file/type | Declaration is edited |
| Export surface | Zero or more boundary/export-binding records, including alias and provenance | A relevant `__init__.spl` export route changes |
| Requester access | Allowed/denied/unknown, reason, route, requester snapshot | Requester or semantic snapshot changes |

Do not store everything as one `is_public` Boolean. Do not implement the new folder default by reusing `pub(package)`: a package can contain multiple directories.

Preserve existing `pub(peer)`, `pub(up)`, `pub(friend)`, and `pub(package)` behavior unless a specific inconsistency is fixed and tested. These are access relations, not necessarily a single total rank. Add the new default distinction without broadening their permissions.

### 4.2 Expected examples

Assume an owner file `app/auth/login.spl`, another file `app/auth/session.spl`, and the boundary manifest `app/auth/__init__.spl`.

| Declaration / export | Same owner file | Same immediate folder | Parent via exported façade | Feature-public | Layer-public |
|---|---|---|---|---|---|
| `fn helper()`; no export | Allowed | Allowed | Denied | No | No |
| `fn helper()`; explicit façade re-export | Allowed | Allowed | Allowed through that binding | No | Yes, for that boundary |
| `pri fn secret()` | Allowed | Denied | Denied; export attempt is an error | No | No |
| `pub fn login()`; no layer export | Allowed | Allowed | Subject to the legal module route, not automatically a façade export | Yes | No for that boundary |
| `pub fn login()`; façade re-export | Allowed | Allowed | Allowed through that binding | Yes | Yes |

Files under `app/auth/internal/` are not in the same immediate folder. Folder-local is based on the compiler's normalized logical source-directory identity, not a raw string-prefix match.

### 4.3 Façade promotion rules

1. An explicit `export use` can expose a folder-local declaration that the manifest itself can legally resolve.
2. Promotion applies to the **exported binding**. The original private implementation path does not become globally public.
3. Explicit `pri` cannot be promoted. A wrapper declared in an allowed scope is a separate explicit programming choice, not something AOP generates.
4. A selected symbol re-export does not also require exposing its whole implementation module with `pub mod`.
5. `pub mod` opens a module route; it does not expose that module's unexported folder-local members indiscriminately.
6. Exporting through one directory does not automatically export through every ancestor. Resolve each relevant boundary and preserve aliases/origin IDs.
7. No `__init__.spl` means no manifest-derived layer export. Existing open-module handling for `pub` can remain, but omitted visibility still means folder-local.
8. Check accessibility of exported signature types, containing types, and members. Do not turn this top-level default change into a silent relaxation of private fields or methods.

The earlier Java comparison is only an analogy for default package-local access. Java packages are not defined simply by filesystem folders, and this plan specifies Simple's own directory semantics. [E05]

### 4.4 Compiler changes

- Introduce an explicit omitted/default visibility tag at parse time; preserve explicit `pri` through parser, Tree-sitter, AST bridges, HIR, imports, serialization, and TLDR.
- Remove unconditional `Public` substitutions where the original declaration/export metadata is available. Bootstrap shortcuts must preserve the same access facts.
- Route access checking through one requester-aware semantic function. Name lookup and access permission are separate operations: finding a sibling symbol does not grant access to an explicit-private symbol.
- Replace filename auto-public ambiguity. The final rule is no modifier = folder-local, including a type that matches its filename. Migration diagnostics can identify former auto-public dependencies; they must not silently defeat `pri`.
- Version old caches that lack declaration intent. Never reinterpret cached `Private` as confidently meaning either default-folder or explicit-private.
- Use one semantic mode for development and release. A staged migration warning policy is separate from build optimization/profile and must be recorded in cache keys.

## 5. Minimal AOP grammar repair

### 5.1 Before and after

Current module-level form:

```simple
on pc{ execution(* app.*(..)) } use trace before
```

Target ownership form:

```simple
aspect Trace:
    on pc{ execution(* app.*(..)) } use trace before
```

The visible change is **ownership under an aspect**, not a redesigned execution signature. Keep the existing `pc{ ... }` delimiter in this change; the aspect body uses normal indentation.

Proposed visibility filtering reuses the existing `attr(...)` selector shape:

```simple
aspect FolderTrace:
    on pc{ execution(* app.*(..)) & attr(layer_public) } use trace before

aspect PublicTrace:
    on pc{ execution(* app.*(..)) & attr(feature_public) } use trace before
```

These are target syntax examples, not claims that the current parser implements them. `layer_public` and `feature_public` here are reserved **compiler-derived attributes**; source code cannot forge them with annotations. There are no new `file_public` or standalone visibility-filter keywords.

`attr(layer_public)` is resolved against the aspect's selected directory scope and the function's export-boundary records. `attr(feature_public)` selects the canonical public-declaration surface. A single Boolean cannot represent every boundary of a multiply re-exported symbol.

Concretely, existing directory/aspect applicability metadata must resolve an explicit set of boundary IDs, `B`, before selection. `attr(layer_public)` matches a callable if at least one of its resolved export bindings belongs to `B`. Retain `B` in the selection digest. It is not inferred from the function-name wildcard, and `within(...)` still filters lexical ownership. An absent/unresolved boundary scope is an error for this filter, not permission to match every ancestor. The debug profile selects `B` from the resolved directory interfaces under its configured roots.

### 5.2 Unambiguous execution syntax

For the supported form `execution(* app.*(..))`:

- The first `*` is the existing wildcard placeholder in the return-position slot. It is **not a class name**, a captured return value, or a request to implement return-type filtering.
- `app.*` is the qualified function-name pattern.
- `(..)` means the existing unrestricted argument-pattern placeholder. It does not bind or capture arguments.
- `trace` remains a parameterless, unit-returning advice function.

Only wildcard signature slots are supported by this scoped implementation. Diagnose concrete return/argument patterns rather than silently ignoring them. A compatibility warning can precede an error for existing sources, but do not add typed matching as the workaround.

### 5.3 Parser and matcher contract

| Issue | Target behavior |
|---|---|
| `execution(` versus `execution (` | Same token sequence and same validation outcome |
| `call(...)`, including with spaces/comments | Rejected for this subset; no accidental alias to execution |
| Boolean operators | Preserve `!`, `&`, `\|`; precedence is not, and, or; parentheses group |
| `within(pattern)` | Lexical owner module/directory selection at compile/load selection time; not dynamic call-stack ancestry |
| `attr(name)` | Actual resolved annotation/derived metadata; never an unconditional false in one execution path |
| Unknown selectors or trailing text | Useful diagnostic with a source span; no silently ignored bare identifiers |
| Advice ownership | `on pc` requires a named owning aspect; carry owner ID through AST/HIR/cache/catalog |
| Existing static advice kinds | Preserve their semantics and tests; do not equate runtime XRay exit with semantic error/success interception |

Use one small token-aware Boolean query representation across compiler, interpreter, validation, and tooling. Avoid parse-to-spaced-string followed by a second ad hoc recognizer. Directory TLDR stores a canonical selector representation/digest and aspect owner, not executable parser state.

A shared lightweight parser is sufficient; no GPU parser feature is required. Any existing SIMD/GPU frontend must produce the same tokens/AST and pass parity tests. GPU execution tracing itself is out of scope.

Migration: diagnose legacy top-level `on pc` and offer a mechanical wrap into a named aspect. During a compatibility window an explicit legacy owner may be retained in metadata, but newly generated code and final strict mode must use named ownership. Do not change unrelated architecture-rule grammar without a separate requirement.

## 6. XRay aspect dynload architecture

### 6.1 Reuse existing owners

The native startup hook, SMF aspect catalog, activation metadata, pin accounting, and loader I/O are useful existing pieces, but they are not one proven XRay path today. Preserve their format/ABI validation and add an execution-observer capability rather than a parallel general-purpose loader.

LLVM XRay supplies compiler-inserted function boundary instrumentation and runtime patch control. Clang or LLVM IR attributes identify candidates; per-function patch APIs enable selected surviving functions. This is the external mechanism being integrated, not a Simple feature already present. [E01], [E02], [E03]

Separate responsibilities:

| Owner | Responsibility |
|---|---|
| Compiler semantic layer | Resolve visibility, owner directory, aspect scope, and candidate membership |
| Backend/link integration | Emit and retain candidate boundaries; bind machine/XRay identities to semantic IDs |
| Existing aspect catalog/loader | Locate/load a pack; check profile, ABI, build identity and capabilities; pin/unpin lifecycle |
| Resident XRay adapter | One process-level handler; safe dispatch publication, event-kind adaptation, patch status, lifetime protection |
| Dynloaded folder-trace aspect | Transition policy, bounded trace consumption, formatting, destination, and debug controls |
| Host-owned tracing storage | TLS POD state and retained buffer lifetime; safe thread detach and quiescence |

The folder logger is not injected as ordinary calls throughout application code. The development binary contains selected patchpoints plus a small runtime adapter; the aspect implements the optional logging concern. A release build excludes this debug dependency closure.

### 6.2 Candidate selection and metadata

Default candidates are the union of layer-exported callable implementations and ordinary public callable declarations under the configured source roots. Aspects may select a subset. Private helpers are not instrumented merely because a public API calls them.

Resolve the set using declaration/export indexes and cached directory summaries. Deduplicate a function reached through multiple aliases or matching multiple rules. Do not traverse every caller or rewrite call sites.

The application catalog needs, at minimum:

- Semantic function identity, defining file/module/directory, and source location.
- Declared visibility and applicable export-boundary identities/provenance.
- Candidate eligibility and supported observation kinds.
- Build fingerprint, target/backend, trace ABI/schema, and post-link instrumentation binding.

XRay IDs are build/runtime instrumentation identities, not stable source IDs. Bind them after final code generation/linking, or during controlled startup from final-image addresses and metadata. Never persist a naked XRay number as a reusable source identity across builds. Use object/load-generation identity too if instrumented target DSOs are supported later.

Changing only the logging aspect body must not require rebuilding already-prepared target functions. An aspect selecting a function with no prepared patchpoint must report it unavailable; it cannot manufacture the pointcut by dynloading alone.

### 6.3 Backend and optimizer constraints

- First acceptance target: a verified hosted LLVM/Clang toolchain with a matching compiler-rt XRay runtime. Probe compile, link, patch, callback, and unpatch behavior—not just a compiler flag.
- If Simple emits C through Clang, carry the same candidate attributes and link policy through that path. Direct LLVM IR emission uses the corresponding function attributes. Both consume one normalized policy.
- Instrumenting a **consumer aspect library** is unnecessary. The logger pack itself should be uninstrumented. Tracing functions inside arbitrary dynamically loaded target libraries is a separate capability, not implied by being able to dynload the logger.
- Candidate functions must survive optimization as observable boundaries. An XRay annotation is not a promise to preserve every source-level function against inlining/LTO. Use a narrowly scoped, measured development boundary-preservation policy, and verify the final binary's candidate map.
- Do not globally disable inlining. Preserve only selected boundary functions where required. Remove the trace-specific preservation policy in release, along with instrumentation.
- Preserve real tail-exit event handling where the chosen XRay runtime exposes it. Disable or diagnose transformations that the v1 observer cannot model accurately.
- Cranelift, GPU targets, SimpleOS/freestanding, and unverified host/CPU combinations report unsupported. Do not enable SimpleOS's currently disabled XRay runtime as an incidental change.

### 6.4 Loading and activation lifecycle

The inspected hosted entry wrapper invokes `__simple_startup_before_main` **before** `__simple_runtime_init`. The new debug observer path must queue/validate an early startup request, then load and activate a Simple-dependent logger only after runtime/TLS initialization is ready, before user `main` if requested. Library constructors matter too: deferring only the explicit initializer is insufficient if loading itself runs runtime-dependent constructors. An early native-only extension requires a separately verified pre-runtime-safe contract. Apply the ready hook consistently to every admitted entry path. [R36]

1. Check profile permission **before** loading a debug pack or running its initializer. Native library constructors can run during load; rejecting registration afterward is too late for release-policy enforcement.
2. Load and validate through the existing loader. Retain the pack and required metadata.
3. Resolve the requested candidate subset; allocate/register bounded trace storage through the owner layer before event delivery.
4. Install or reuse the resident dispatcher. Publish a protected generation containing a complete immutable lookup/dispatch view.
5. Patch selected functions and verify each result. Multiple-function patching is not atomic; mark the activation window as partial/unknown. A failed patch produces failed/explicitly partial activation, not full success; roll back only patches owned exclusively by this activation when safe.
6. Enable event recording only under the published generation. Report separate states for loaded, prepared, active, disabling, quiescing, and unloadable.

On disable, gate that aspect's recording, remove its observer membership, and retire its dispatch generation. The host owns per-function subscriber membership/counts: unpatch a function only when the last active observer releases it. Other aspects sharing a candidate must remain operational. Acknowledging “recording stopped” is not the same as proving “all callbacks and workers have quiesced.”

An unpatch failure leaves a prepared function capable of invoking the resident handler. Report recording-disabled separately from unpatched; retain the handler and required metadata until physical patch state is known. A failed unpatch must never justify freeing its dispatch state or claim the callback-free disabled-cost budget. Serialize control-plane registration/patch/unpatch/publication transitions, bound observer fan-out as well as retained generations, and keep blocking lifecycle work off the callback path.

On unload, wait for protected readers, callbacks, buffer consumers, and worker code to release the retired generation. A pointer load followed by an unprotected reference-count increment is not safe. Reuse a reviewed protected-acquisition/epoch or pin mechanism. If quiescence times out, retain the disabled pack and report why; never force-close executable code still in use.

Keep one resident XRay handler and multiplex registered aspects through it. Packs must not independently overwrite a global handler. Preserve independent per-aspect observation state when candidate sets differ; do not reuse a stack built from an incompatible selection. Bound retained generations within the total trace-memory cap and reject a reload when old readers prevent safe reclamation. Exclude the entire tracing dependency closure from instrumentation and use a reentrancy guard.

### 6.5 Preserve the requested advice ABI

Language advice remains parameterless and unit-returning. The internal loader/observer ABI carries function IDs and event kinds; it is not language-level capture of arguments or results.

The folder logger internally observes paired entry/exit events to maintain context. That bookkeeping does not add a new `after` grammar form. XRay normal exit must not be advertised as semantic `after_error` or proof that a returned `Result` is successful. A function returning an error value still exits normally. Keep existing static advice semantics separate; reject unsupported dynamic forms instead of guessing.

## 7. Thread-local folder transition logging

### 7.1 Directory identity

At build/index time, derive a canonical logical identity from package/source-root identity plus the normalized source-relative directory path. Normalize separators and dot segments consistently with the compiler; do not lowercase case-sensitive names or embed developer-machine absolute paths.

Use the project's XXH3-128 implementation for fast directory identity where available, then intern verified identities into compact dense runtime IDs. Hash collisions must be checked against the full canonical identity during build/load. A truncated hash is not a unique directory ID by itself.

This directory hash is not a pack-integrity or security digest. Preserve existing cache/pack integrity algorithms; there is no global hash-system migration in this plan.

Hot-path lookup is a bounded array/table access from instrumentation ID to compact owner-directory metadata. There is **no per-event path hashing, path-prefix parsing, symbolization, regex matching, or filesystem access**.

### 7.2 What TLS tracks

Per attached thread, maintain a bounded state containing:

- Activation generation and trace/context-validity state.
- Reentrancy guard and dropped-event/context-reset counters.
- Observed selected-function depth.
- A bounded stack of function/owner-directory IDs, including same-directory frames.
- A retained host-owned event-buffer reference.

Use the existing runtime threading/TLS owner. This is not a request for a new source-language TLS keyword. Provision storage before tracing a thread, or fail attachment nonblockingly; the first XRay callback must not trigger allocator recursion or unsafe lazy initialization.

### 7.3 Entry and exit rules

On an observed entry:

1. Validate generation and lookup the callee's canonical owner directory.
2. Compare against the top **observed** frame, or unknown context if none is valid.
3. Push every selected frame, even if no log will be emitted. Increment observed depth.
4. Emit a compact transition record if directories differ. Emit a depth-only record only when that verbose option is explicitly enabled.

On an observed exit:

1. Validate the expected frame/event kind.
2. Pop the frame and restore the previous observed context/depth.
3. Emit the reverse transition if the owner directory changes.
4. On unmatched exit, overflow, or known discontinuity, mark a gap/reset. Do not fabricate a matching entry, caller, or return.

For example, selected calls `ui.open -> service.load -> db.read` and their normal returns can produce:

```text
thread=7 event=enter  from=unknown     to=app/ui       observed_depth=1
thread=7 event=enter  from=app/ui      to=app/service  observed_depth=2
thread=7 event=enter  from=app/service to=app/db       observed_depth=3
thread=7 event=return from=app/db      to=app/service  observed_depth=2
thread=7 event=return from=app/service to=app/ui       observed_depth=1
thread=7 event=return from=app/ui      to=unknown      observed_depth=0
```

These are formatted outputs produced outside the callback, not synchronous `print` calls in the instrumented function.

### 7.4 Truthful limits

- Public-boundary depth is **observed depth**, not full machine/source call-stack depth. `public A -> private B -> private C -> public D` can show depths 1 and 2.
- Sparse observation does not identify the immediate caller. If an uninstrumented frame crosses another folder, the log describes consecutive observed contexts, not every actual folder transition.
- Function execution cannot identify which façade alias invoked a shared implementation. Selection uses export provenance, but runtime attribution uses the defining owner directory.
- Source path nesting depth is not call depth. Do not confuse “three directory components” with “three active functions.”
- Thread-local is not task-local. Known fiber/task switches must reset/mark the affected thread context; do not silently stitch independent tasks into one call chain. Task-local correlation remains deferred.
- Normal returns, tail exits, error-value returns, native unwinding, nonlocal jumps, thread exit, and process termination need different accounting. Missing events require explicit partial-trace status.
- Activating or disabling while frames are already active cannot reconstruct the missing stack. Epoch changes establish a new partial observation interval.

### 7.5 Bounded buffering and output

Record fixed-size numeric events into a nonblocking bounded buffer. Format directory names and write output in an uninstrumented consumer. Keep compiler stdout, language-server JSON-RPC stdout, and MCP protocol stdout untouched; use a dedicated trace sink/file or explicitly configured diagnostic stderr.

Bound both per-thread storage **and total process trace memory/thread attachments**. Otherwise a per-thread cap still permits unbounded growth with thread creation. A full queue drops records and increments counters; it never blocks application progress. A full context stack invalidates depth until a safe reset; it must not simply skip one push and continue claiming balanced nesting.

Buffers outlive queued consumption. A sink must not retain a pointer into destroyed TLS after a thread exits. Detach/drain safely or use independently retained host-owned storage. Sink failure, disk-full conditions, reentrancy, and logging shutdown must not recurse through ordinary application logging.

Default policy: log folder changes and include observed depth on those records. Same-directory events update state without output. An explicit depth-all option logs every observed depth change and has correspondingly higher event/output cost.

## 8. Build options and phase 3 / phase 4 policy

### 8.1 One typed configuration owner

Extend the existing `CompileOptions`/normalization owner. Do not create separate shell-only, environment-only, and LSP-only interpretations of development versus release.

Proposed user-facing controls are a development profile option, the existing release option, a folder-trace enable/disable debug option, and a depth-output policy. Exact CLI spellings must be registered once in the existing option parser/help/completion; examples below describe the intended SDN policy, not already-supported settings.

```sdn
bootstrap_profiles:
  phase3:
    build_mode: debug
    profile: dev
    debug_aspect_dynload: true
    folder_trace: true
    depth_output: transitions
    instrumentation: xray_boundaries
  phase4:
    build_mode: release
    profile: prod
    debug_aspect_dynload: false
    folder_trace: false
    depth_output: none
    instrumentation: none
```

Optimization remains a separate typed field. An optimized development build must remain development; `opt_level > 0` must no longer silently select release. A request combining release and enabled debug folder tracing is a configuration error, not “last flag wins.”

Track requested policy and resolved target capability separately. A non-XRay backend cannot claim `instrumentation=xray_boundaries` in a receipt simply because the requested profile said development.

For phase-3 compiler/tool artifacts, start with the program's owned application/compiler roots. Include dependency roots only when explicitly selected, and always exclude the tracing/TLS/allocator/sink closure. “All public functions” means all eligible functions in the selected roots, not every linked system library.

### 8.2 Managed and legacy bootstrap paths

Current managed phase construction uses release for both phases, while `bootstrap-phase4-grouped.shs` generates the same general `native-build ... --mode dynload` shape. Update all of:

- Phase authority creation and verification.
- Phase index configuration and normalized variant identity.
- Provisional authority/resume paths.
- Grouped build command manifests and target artifact receipts.
- Legacy bootstrap continuation and delegating platform wrappers.
- Tool binaries and packaging paths that inherit phase policy.

The active bootstrap script hands off to a managed scheduler before its legacy stage-3 block. Managed phase 4 can use an admitted producer without waiting for phase 3. Therefore:

> The rule applies to the **artifact being built**, not automatically to the profile of the compiler process building it.

Record producer identity separately from target profile. Do not change the scheduling graph solely to enforce this option split. Retain existing source-snapshot, toolchain, ABI, freshness, and publication admission checks.

The existing diagnostics switch enables tracing/profile/IR/memory diagnostics; it is not a substitute for an explicit development artifact profile.

### 8.3 Cache and resume identity

Add normalized policy to every affected variant/action/object identity:

- Target profile and semantic visibility version.
- Backend/toolchain/target and verified XRay capability variant.
- Instrumentation kind, candidate-set digest, and boundary-preservation policy.
- Trace metadata/ABI schema and export-surface digest where relevant.
- Aspect interface/selector digest, distinct from its implementation body digest.

Runtime on/off state and trace sink filename must not force target recompilation when the prepared candidate set is unchanged. Conversely, a release object must never be reused as XRay-ready, nor a development instrumented object as release, even when source timestamps match.

Reject stale retained job manifests/receipts after the profile schema change. Do not resume a previous “both release” job under new phase-3 development assumptions.

### 8.4 Release enforcement

For phase 4, omit the XRay boundary instrumentation, directory trace map, debug pack dependency, trace-specific boundary-preservation attributes, and debug-aspect startup path. The release artifact must not be merely a development artifact with recording set to false.

Gate the current startup-aspect environment/option route before debug code is loaded. Include `--startup-extension=PATH` and `--startup-extension PATH`, not only the environment variable. Establish debug-versus-functional pack classification through a host-controlled route or validated pre-load metadata; inspecting an initializer/export after `dlopen` is too late to prevent constructors. Preserve permitted functional startup-extension behavior with a separate regression fixture. A release binary must not activate this debug facility through `SIMPLE_STARTUP_ASPECTS`, `SIMPLE_AOP_DEBUG`, an explicit debug-aspect request, or XRay environment settings. Ordinary native/SMF component loading remains a separate supported capability.

An arbitrary library loaded through a general-purpose loader can execute arbitrary native code; this release policy is not a sandbox that prevents every possible plugin from printing. Its guarantee is that **the supported optional debug-aspect/XRay path is absent or denied**.

Artifact checks must inspect final code/sections and dependency closure, not just search user-visible log strings. On supported ELF targets inspect the XRay instrumentation map/sections and relevant runtime symbols; adapt equivalent checks per admitted target rather than hard-coding ELF assumptions everywhere.

Cross-profile phase-3/phase-4 hashes are expected to differ. Preserve bootstrap admission/self-host tests, and add reproducibility checks using the **same source entry, target, and profile**. The legacy stage comparison is only a warning today; do not describe it as an existing strict fixed-point proof.

## 9. LSP and MCP visibility improvements

### 9.1 Current answer to “is it properly implemented?”

**Partly implemented, but not correct enough for this requested model.** There are real visibility views and request routes; the gaps are semantic consistency, propagation, live buffers, and query architecture—not merely missing labels.

Specific mismatches include:

- Current `featurePublic` means MDSOC capsule export/exposed-port membership, sometimes augmented by requester-local reachability.
- Current “public” sets can contain symbols reachable only because the requester shares a boundary. Changing requester should change reachability, not declaration-public classification.
- Some query adapters reconstruct declared/surface/reachable fields from one Boolean.
- Text scanning and name-only matching cannot reliably distinguish aliases, shadowed names, overloads, multiline exports, or a full chain of boundaries.
- The inspected live `didChange` handler does not maintain unsaved source state.
- Hover/completion/visibility routes can spawn processes and reread manifests per request.

### 9.2 Canonical response model

Use the same semantic snapshot as compiler access checking. Each symbol result should carry:

| Field/concept | Meaning |
|---|---|
| Symbol identity | Owner-qualified semantic ID; never just a short name |
| Declared visibility | Default-folder / explicit-private / public / existing scoped modifier |
| Feature-public | Canonical ordinary-public declaration classification requested in this session |
| Layer export bindings | Boundary IDs, aliases, origin ID, and `__init__.spl` source locations |
| Requester result | Allowed/denied/unknown with route and reason; omitted/unknown if requester is unspecified |
| Legacy capsule export | Separately named MDSOC capsule metadata, not silently deleted or redefined |
| Snapshot/version | Source and manifest versions used to produce the answer |

Version the existing experimental visibility response. Preserve legacy MDSOC meaning under an explicit `capsuleExported`-style field or legacy-version adapter; migrate consumers and tests before changing the old field's meaning. New unambiguous fields should be available during migration.

### 9.3 User-visible views

Use standard hover/document-symbol/completion details for a useful baseline. Custom semantic-token modifiers are optional negotiated enhancements, not a required client feature. Do not encode visibility using an unrelated standard tag such as deprecated. LSP remains JSON on the wire; SDN remains the default for Simple configuration and internal records. [E04]

Illustrative hover for a folder-local function exported by a façade:

```text
helper()
Declared: folder-local (no modifier)
Layer export: app.auth.helper
Exported by: app/auth/__init__.spl
Feature-public: no
Access from app/main.spl: allowed via app.auth.helper
Direct implementation path: not public
```

Illustrative hover for a `pub` declaration hidden by a closed module route:

```text
login()
Declared: public
Feature-public: yes
Layer export at app.auth: none
Access from requester: denied by the module boundary
```

Completion uses requester access to hide or clearly mark unusable suggestions. Workspace navigation may still list an inaccessible declaration with an accurate label; source browsing is not permission to compile a reference. Go-to-definition should retain the original declaration, while export provenance offers navigation to the relevant façade.

No-requester queries return stable public-surface classifications, not an invented “same file” requester. The existing last-read requester convention can remain only when it is explicitly reported as such.

### 9.4 Live documents and performance

- Maintain versioned open-document overlays for source and `__init__.spl`; apply the synchronization mode actually negotiated with the client.
- Update parser/semantic snapshots on edits and discard stale asynchronous results. Respect LSP position encoding rather than assuming byte offsets.
- Recompute only affected export/dependency slices. Reuse the existing directory index and TLDR cache; do not add per-hover whole-tree scanning.
- Replace visibility hot-path subprocess/text scraping with a resident snapshot adapter/shared semantic service. A one-shot CLI may load the same cache, but must not define different visibility semantics.
- On stale/incomplete metadata, return pending/unknown with provenance rather than claiming public or accessible.
- Test native LSP, MCP visibility tools, CLI queries, and compiler diagnostics against the same fixture/result corpus.

## 10. TLDR, reverse references, and incremental compilation

Directory TLDR should summarize the resolved interface and relevant aspect selection. It must not execute source generation or insert functions itself. The earlier getter/setter-generation discussion is deferred; no hidden accessor is generated by this plan.

Persist:

- Exact declared visibility and owner IDs.
- Boundary export bindings, aliases, origin IDs, and resolved interface digest.
- Canonical pointcut query/digest and owning aspect ID.
- Candidate-group membership and the instrumentation/visibility schema version.

Use existing canonical cache encoders. The current AOP implementation/interface digest split is valuable; keep aspect body changes separate from selector/interface changes. Replace textual selector normalization with semantic/token normalization when the shared parser lands, and bump the matcher schema.

| Change | Required invalidation | Avoid |
|---|---|---|
| Logger body or formatter changes | Pack rebuild/reload, ABI compatibility check | Rebuilding all target functions when patchpoints are unchanged |
| Pointcut or aspect scope changes | Relevant directory candidate groups; target rebuild only for new/removed required instrumentation | Whole-repository caller traversal |
| `pub`/`pri`/default visibility edit | Owner semantic/TLDR slice, affected importers, views and candidate groups | Treating it as a body-only edit |
| `__init__.spl` export edit | Directory interface, dependent boundary routes, affected objects/views/candidate maps | Ignoring transitive export aliases |
| Source directory move | Old/new owner identity and dependent routes; new final-image map | Interpreting it as an event in an already-running old binary |
| Runtime recording toggle | Activation generation/state only | Rewriting TLDR or rebuilding code |
| Development/release profile change | Separate variant/object/link products | Reusing the other profile's artifacts |

Keep consumer edges/counts in the planned `.rr` reverse-reference index, not in frequently rewritten public TLDR interfaces. Where the existing cache plan uses host atomic writes through sosix, reuse that owner and its failure policy. A failed/corrupt `.rr` publication must mark the dependency snapshot untrusted and trigger authoritative reconciliation before it can justify cache reuse.

For a changed directory interface, conservatively invalidate all affected files in that directory and dependent export/import routes unless a precise, tested dependency slice proves a smaller set. Cache correctness takes precedence over optimistic reuse; body-only changes and runtime toggles must still avoid unnecessary interface churn.

## 11. Build cost, runtime overhead, memory, and performance

### 11.1 Separate selection cost from event cost

Let `F` be candidate function declarations, `S` potential call sites, `E` observed runtime entry/exit events, and `T` attached threads. These are different dimensions; a selector being cheap to match does not make active tracing free.

| Mechanism | Build/selection work | Disabled runtime | Enabled runtime | Extra memory/code |
|---|---|---|---|---|
| `execution` selection | Indexed declaration filtering; generally scales with relevant `F` | No selector matching per call | Events at selected executions | Candidate metadata and selected sleds |
| `within`, visibility-derived `attr` | Resolve against semantic/module/export metadata | No runtime predicate evaluation | Already represented in selected IDs | Compact metadata; no per-call path strings |
| Directory-change policy | Build/load directory-ID table | No handler when unpatched | Lookup, TLS push/pop, compare; buffer only selected output | Bounded TLS/buffers plus map |
| Every-depth-change output | Same candidate preparation | No handler when unpatched | Output event on essentially every observed entry/exit | Higher buffer pressure and sink traffic |
| `call` if implemented later | Call-site work can scale with `S`, including optimization/cloning concerns | Depends on the future patching scheme | Depends on selected sites and required caller context | Can grow per call site rather than per function |
| Generated `get`/`set` if implemented later | Field-access lowering and accessor eligibility | Preserved accessor boundaries can still cost | Potentially very high event rate | Accessor code/maps; optimizer constraints |

The last two rows are comparisons only, not implementation tasks. Do not claim universally fixed performance ratios without measurement. An execution hook may observe the same number of invocations as a call hook; call-site specificity and code multiplicity are the key additional burdens.

### 11.2 Runtime modes

| Mode | Cost/guarantee |
|---|---|
| Release, statically off | No instrumentation or debug-folder-trace code in the supported path; ordinary application logging/dynload unaffected |
| Development ready, disabled | Retains prepared code/metadata and any selected no-inline policy; no event callbacks when unpatching succeeds |
| Development active, same folder | Per-event adapter/TLS accounting; normally no output record |
| Development active, changed folder | Accounting plus one compact record; formatting outside the callback |
| Development active, all-depth output | More records; must be presented as a verbose/high-volume debug mode |

Benchmark three different effects separately: instrumentation/boundary preservation versus an otherwise comparable build, active callbacks versus the same prepared-but-disabled build, and output/formatting versus recording alone. Comparing only development against optimized release cannot isolate XRay overhead.

### 11.3 Proposed budgets, not measured results

- Release structural budget: zero debug candidate sleds/maps and zero supported debug activation routes. No per-function branch is acceptable as the substitute for static removal.
- Active callback: no allocation, blocking lock, filesystem access, string formatting, symbolization, or recursive logging. Verify with counters/probes, not only code inspection.
- Memory: require a configured process-wide cap; an initial hosted default of 32 MiB is a proposal, including maps, retained generations, stacks, and queues. Refuse or degrade attachment explicitly before exceeding it. Record actual per-thread and total usage.
- Warm visibility queries: no subprocesses and no full-tree reads. Initial target is p95 under 50 ms on a recorded workstation/fixture; report fixture size, sample count, cold-start cost, and max RSS. This is an acceptance target, not a claim about current performance.
- Build/runtime regression thresholds must be set from a retained baseline on the supported target. Initially investigate more than 5% additional candidate-preparation build time or more than 3% disabled-prepared throughput loss on representative workloads; selected boundary preservation may dominate and must be reported separately rather than hidden.
- Test 1, 2, and many threads, cold/warm builds, small and large candidate sets, rapid toggles, and a slow/failing sink. Publish dropped-event counts alongside trace results.

## 12. Implementation ownership and work packages

### 12.1 Source ownership map

| Owner | Existing source areas to change/extend |
|---|---|
| Declaration visibility contract | `src/compiler/00.common/dependency/visibility.spl`, `src/compiler/00.common/visibility.spl` |
| Parser/AST and Tree-sitter | `src/compiler/10.frontend/core/_ParserDecls/`, `src/compiler/10.frontend/parser_types.spl`, `src/compiler/10.frontend/treesitter/outline_decls.spl` |
| Pointcut representation/matcher | `core/aop_predicate_parser.spl`, `core/aop.spl`, `src/compiler/80.driver/driver_pipeline_aop.spl` |
| HIR propagation/access checks | `src/compiler/20.hir/hir_lowering/_Items/`, `src/compiler/35.semantics/visibility_checker.spl`, `visibility_integration.spl` |
| Static weaving compatibility | `src/compiler/50.mir/mir_aop_injection.spl`; preserve its ABI and static semantics |
| Catalog and loader | `src/lib/common/aspect_pack.spl`, `src/compiler/99.loader/aspect_pack_io.spl`, `src/runtime/runtime_native.c` |
| XRay adapter/emission | Add a thin owned adapter at the runtime ABI boundary and extend the relevant admitted LLVM/Clang backend; new bridge, not an existing feature |
| Folder-trace concern | New debug-aspect module/pack; retire the overlapping global-state folder-trace path in `core/aop_debug_log.spl` without deleting unrelated debugger consumers |
| Semantic visibility views | `src/app/cli/_QueryVisibility/`, `src/compiler/90.tools/query_helpers.spl`, `src/app/simple_lsp_mcp/`, `src/lib/nogc_sync_mut/lsp/` |
| Cache/TLDR | `src/compiler/85.mdsoc/aop_cache/`, existing package TLDR/variant owners, `src/compiler/80.driver/driver_build/incremental.spl` |
| Profiles/bootstrap | `src/compiler/00.common/driver_compile_options.spl`, `src/app/io/_CliCompile/`, `src/app/bootstrap_builder/`, `scripts/bootstrap/` |
| Formal contract | `src/verification/visibility_export/src/VisibilityExport.lean` plus executable compiler/model correspondence fixtures |

Keep dependencies directional. AOP core must not depend on the folder logger. Protocol-only LSP libraries must not import the whole compiler; the application composition root wires a canonical semantic snapshot provider into the LSP adapter. The runtime adapter must not perform compiler/name-resolution work per event.

### 12.2 Ordered implementation work

| Work package | Deliverable | Depends on | Relative effort |
|---|---|---|---|
| W0: Freeze contracts and baseline | Requirement/test manifest, source/profile baseline, exact knowledge route, failure reproductions | None | S |
| W1: Visibility intent and access | Default-folder versus explicit-private propagation, export-binding resolver, access parity | W0 | L |
| W2: Grammar/matcher ownership | Shared query parser, whitespace fix, `within`/`attr` parity, aspect IDs and migration diagnostics | W0; W1 for visibility attributes | M |
| W3: Metadata and cache | Versioned visibility/TLDR/export/selector metadata and post-link candidate binding contract | W1–W2 | M |
| W4: XRay loader bridge | Capability probe, candidate emission, resident dispatcher, protected lifecycle | W3; early W6 profile/load gate | L |
| W5: Dynloaded folder logger | Bounded TLS observation, transition/depth policy, safe consumer and controls | W4 | M |
| W6: Phase/profile enforcement | First normalize profile and gate pre-load permission; then managed/legacy routing, receipts, static-off artifact enforcement | W0 for early gate; W3–W5 for full integration | M–L |
| W7: LSP/MCP semantic views | Versioned labels/access/provenance, overlays, resident queries | W1–W3 | L |
| W8: Acceptance and proof alignment | End-to-end tests, source-model correspondence, performance/artifact evidence | W4–W7 | M–L |

Effort bands are planning estimates, not delivery dates. Parser spelling repair is smaller than visibility propagation, native lifecycle safety, or fixing live-buffer/query architecture. W6 profile normalization/pre-load gating starts before native activation; remaining profile plumbing and W7 views can proceed in parallel after the shared contracts stabilize; final integration belongs to one owner.

The selected approach is direct execution instrumentation: low selection complexity and no caller rewriting, but it only observes prepared surviving functions. The alternative of call-site or accessor weaving offers more detail at the cost of broader compiler changes and is explicitly deferred, not left as an implicit implementation option.

## 13. Acceptance tests and verification plan

All rows below are **planned tests**, not reported passes. Use real compile/run/protocol/artifact assertions. An unavailable toolchain/target is unavailable, not a passing no-op.

### 13.1 Grammar and visibility matrix

| Test ID | Requirement | Concrete expected result |
|---|---|---|
| G01 | A02 | `execution(` and `execution (` produce the same canonical query and diagnostics; unknown selectors are rejected with either spacing |
| G02 | A02 | `!`, `&`, `\|`, grouping, comments, and source spans agree across parser, interpreter, compiler, and tooling |
| G03 | A02 | Positive/negative `within` and `attr` fixtures match real owner/attribute metadata; neither silently returns false everywhere |
| G04 | A02 | Top-level `on pc` receives the chosen migration diagnostic; named aspect ownership survives AST/HIR/cache/catalog round trips |
| G05 | A02–A03 | `call`, `get`, `set`, typed signature filtering, non-unit advice, and parameterized advice are rejected in this new subset |
| V01 | V01 | Unmodified top-level function is usable from the same directory but not an unexported parent/subdirectory route |
| V02 | V01 | Explicit `pri`, including filename-matching types/functions, remains private on every import/lowering path |
| V03 | V02 | Explicit façade re-export promotes a folder-local binding without exposing its original implementation path or whole module |
| V04 | V02 | Exporting explicit-private fails; exported signatures using inaccessible types fail appropriately |
| V05 | V02 | `pub mod` and selected re-export are independent; a public module does not expose all folder-local members |
| V06 | V02 | Multiple aliases/boundaries retain the same origin ID with distinct binding provenance; ancestor restrictions remain enforced |
| V07 | V01–V02 | Existing peer/up/friend/package rules retain their intended behavior; same-folder is not widened to whole package |
| V08 | V02, A02 | One implementation exported through two boundaries matches `attr(layer_public)` only for the selected boundary set; requester changes do not alter selection |

### 13.2 Runtime and lifecycle matrix

| Test ID | Requirement | Concrete expected result |
|---|---|---|
| T01 | A01, T01 | Real dev binary loads the trace pack, patches the selected IDs, and records the expected entry/return sequence |
| T02 | T01 | Same-directory recursion pushes/pops correctly; later cross-directory returns restore the right observed parent |
| T03 | T01 | Concurrent threads have independent depths/stacks; no process-global interleaving corruption |
| T04 | T02 | Mid-stack enable/disable, repeated generations, partial patch failures, and concurrent control requests produce safe partial/reset status |
| T05 | A01, T02 | Unload waits for callbacks/queued workers; timeout leaves a disabled retained pack rather than unloading live code |
| T06 | T02 | Stack/queue/thread/global-memory limits do not block or exceed the cap; gaps and dropped events are visible |
| T07 | T02 | Thread exit with queued output does not retain dangling TLS pointers; sink failure and reentrancy do not recurse |
| T08 | T02 | Normal/tail exits, error-valued returns, unwind/nonlocal exits, and known task switches are accounted for or explicitly marked unsupported/partial |
| T09 | A01 | Selected development boundaries survive the intended optimizer/LTO policy; missing instrumentation is a failed candidate check |
| T10 | T01 | Re-export aliases of one implementation do not generate invented call-site/alias information |
| T11 | A01, T02 | Two overlapping aspects can be enabled/disabled/unloaded independently; shared functions stay patched until the last observer releases them |
| T12 | A01 | Runtime/TLS initialization precedes Simple-dependent pack constructors, logger storage/worker startup, and event delivery on every supported entry route |
| T13 | A01, T02 | Injected partial patch failure is reported accurately and rolls back only exclusively owned patches without disrupting other observers |
| T14 | A01, T02 | Injected unpatch failure reports disabled-but-still-patched accurately; resident dispatch/metadata remains valid and no callback-free cost claim is made |
| T15 | A01, T02 | Concurrent enable/disable/reload requests serialize control transitions; observer/generation caps reject excess work without callback allocation or use-after-free |

### 13.3 Profiles, tooling, and caches

| Test ID | Requirement | Concrete expected result |
|---|---|---|
| B01 | B01 | Phase-3 command, normalized options, receipt, cache key, and final artifact all identify development; folder-trace option is enabled on a supported target |
| B02 | B01 | Phase-4 equivalents identify release; optimization options cannot accidentally change the requested profile |
| B03 | B02 | Release artifact lacks the debug patchpoint/map/dependency closure and refuses every supported debug activation route |
| B04 | B02 | Ordinary release component/SMF/native dynload remains functional |
| B05 | B01, C01 | Managed scheduling, legacy continuation, resume, and wrappers retain identical profile semantics; stale profile receipts are rejected |
| B06 | B01–B02 | Optimized development remains development after CLI and central normalization; both startup-extension argv forms obey pre-load debug gating while functional extensions still work |
| L01 | L01 | Compiler verdicts equal LSP/MCP requester-access results across the full visibility matrix |
| L02 | L01 | Public surfaces remain stable when requester changes; only access result/reason changes |
| L03 | L01–L02 | Unsaved declaration and `__init__.spl` edits update hover, completion, tokens, diagnostics, and provenance consistently |
| L04 | L01 | Aliases, duplicate short names, multiline exports, closed ancestors, no requester, and legacy capsule data are represented correctly |
| L05 | L02 | Warm visibility paths launch no child processes, perform no full-tree scan, and meet recorded latency/RSS targets |
| C01 | C01 | Logger-body-only edit reloads its pack without changing prepared application objects |
| C02 | C01 | Visibility/export/candidate edits invalidate the expected dependency slice; profile changes cannot hit the other profile's cache |
| C03 | C01 | Failed/corrupt `.rr` state cannot justify stale reuse; reconciliation restores the correct dependency snapshot |
| C04 | C01 | Canonical whitespace-equivalent selectors share a digest; semantically different owners/exports/policies do not |
| C05 | C01 | Exercised cache producers/consumers use real versioned profile/selector/export identities; no sentinel pre-weave key is admitted as evidence of a valid artifact |

### 13.4 Existing tests to extend

- `test/01_unit/compiler/frontend/aop_predicate_parser_spec.spl`
- `test/01_unit/compiler/frontend/core/aop_pointcut_matcher_parity_probe.spl`
- `test/01_unit/compiler/frontend/parser_aop_arch_decl_owner_spec.spl`
- `test/01_unit/compiler/parser/treesitter_visibility_spec.spl`
- `test/01_unit/compiler/dependency/visibility_integration_spec.spl`
- `test/01_unit/app/cli/query_visibility_feature_spec.spl`
- `test/01_unit/app/simple_lsp_mcp/lsp_visibility_requester_spec.spl`
- `test/01_unit/lib/aspect_pack_lifecycle_spec.spl`
- `test/01_unit/lib/aspect_pack_final_unpin_v2_spec.spl`
- `scripts/check/check-startup-aspect-dynload.shs`

These paths were found in the audited tree. Their existence does not establish coverage of the new behavior. Prefer the canonical `test/01_unit` tree over duplicated historical test paths.

Add integration/system fixtures for the new native trace pack, profile artifacts, compiler/LSP parity, and live-document updates. Mirror executable SSpec scenarios under the corresponding generated `doc/06_spec/...` Markdown path; do not place executable tests under `doc/06_spec`.

The primary system scenario should read as an operator flow: build development, observe folder transitions, disable/re-enable safely, replace the aspect, inspect visibility before/after an unsaved export edit, build release, prove debug activation is unavailable, and confirm ordinary program/dynload behavior remains intact. Capture logs, protocol responses, artifacts, and performance data—not only screenshots.

### 13.5 Formal model alignment

The existing binary visibility proof cannot establish the richer implementation's correctness by itself. Extend the model with explicit default/private/public intent, owner identities, export bindings/aliases, and requester access relations.

Prove/test at least:

- Explicit private is not widened by a filename match or re-export.
- Folder equality, not directory-prefix similarity, grants default access.
- A legal façade export grants access to its binding, not arbitrary access to the origin path.
- Public-surface classification is independent of requester.
- Alias chains preserve symbol identity and cannot bypass a closed boundary.
- Compiler, TLDR, and query adapters preserve the same resolved visibility facts.

Use executable correspondence/property fixtures driven by the actual Simple semantic structures and functions. A separately maintained proof with a different `SymbolId` or simplified export rule is not evidence that the production checker is correct. Runtime patching/unloading still requires native integration and concurrency tests; no visibility proof substitutes for those.

## 14. Completion and rollout criteria

1. Freeze the shared semantics and add reproducing tests before changing the compiler or query schemas.
2. Land visibility/matcher schema changes with cache invalidation and compatibility diagnostics; update canonical parser, Tree-sitter, compiler, and views together.
3. Admit one real XRay-capable hosted target first. Record unsupported targets explicitly; do not silently substitute static logger calls.
4. Make phase 3 development and phase 4 release routing observable in manifests and final-artifact checks before default-enabling the debug aspect in normal bootstrap use.
5. Measure build cost, disabled/active runtime cost, memory limits, and LSP performance. Fix meaningful regressions or retain a concrete blocker; do not label an unmeasured target “low overhead.”
6. Pass the acceptance matrix with retained evidence and real assertions. Update help, grammar docs, support matrix, visibility docs, and the existing dynload plans to the same status.
7. Complete a same-profile self-host/reproducibility check where applicable, plus core compiler/lib and MCP/LSP smoke coverage using the admitted self-hosted toolchain—not a seed-only success.

This plan is complete as a design deliverable. The software feature is not complete until the implementation and evidence above exist. No compiler/LSP correctness, XRay capability, release readiness, or benchmark pass is claimed by this document.

## 15. Evidence and source references

### 15.1 Pinned repository sources

Links below are pinned to the audited commit, not a moving branch. Line ranges identify the inspected seam; they do not imply that every execution path was tested.

| Ref | Inspected source | Relevant lines |
|---|---|---|
| [R01] | Native startup aspect loader — `src/runtime/runtime_native.c` | 18265-18385 |
| [R02] | Aspect catalog and lifecycle — `src/lib/common/aspect_pack.spl` | 90-104; 1747-1788; 3130-3176 |
| [R03] | SimpleOS compiler-rt capability configuration — `src/os/port/llvm/compiler_rt_cmake.cmake` | 28-35 |
| [R04] | Pointcut validation — `src/compiler/10.frontend/core/aop_predicate_parser.spl` | 45-87 |
| [R05] | Pointcut evaluator — `src/compiler/10.frontend/core/aop.spl` | 382-399 |
| [R06] | Advice record — `src/compiler/10.frontend/parser_types.spl` | 638-644 |
| [R07] | Existing global-state debug logger — `src/compiler/10.frontend/core/aop_debug_log.spl` | 35-61 |
| [R08] | Top-level visibility parser — `src/compiler/10.frontend/core/_ParserDecls/enum_module_body.spl` | 483-508; 1911-1919 |
| [R09] | HIR directory-sibling resolution — `src/compiler/20.hir/hir_lowering/_Items/module_import_resolution.spl` | 86-99; 599-658 |
| [R10] | Production visibility checker integration — `src/compiler/35.semantics/visibility_integration.spl` | 168-199 |
| [R11] | Visibility/export contract — `src/compiler/00.common/dependency/visibility.spl` | 21-38; 302-339 |
| [R12] | Existing feature-capsule classification — `src/app/cli/_QueryVisibility/feature_visibility.spl` | 3-14; 135-154 |
| [R13] | Live LSP handlers — `src/lib/nogc_sync_mut/lsp/lsp_handlers.spl` | 100-144; 381-428; 519-549 |
| [R14] | CLI native-build options — `src/app/io/_CliCompile/compile_targets.spl` | 877-878; 1069-1108; 1339-1341 |
| [R15] | Managed phase authority — `src/app/bootstrap_builder/native_group_phase2_authority.spl` | 91-98 |
| [R16] | AOP cache group keys — `src/compiler/85.mdsoc/aop_cache/aop_group_keys.spl` | 1-29; 36-76 |
| [R17] | Existing formal visibility model — `src/verification/visibility_export/src/VisibilityExport.lean` | 11-14 |
| [R18] | Pointcut token serialization — `src/compiler/10.frontend/core/_ParserDecls/bitfield_aop_arch_decls.spl` | 188-222 |
| [R19] | Driver AOP context — `src/compiler/80.driver/driver_pipeline_aop.spl` | 110-111 |
| [R20] | MIR advice ABI — `src/compiler/50.mir/mir_aop_injection.spl` | 237-249 |
| [R21] | HIR declaration bootstrap shortcut — `src/compiler/20.hir/hir_lowering/_Items/module_declarations_bootstrap.spl` | 149-159 |
| [R22] | HIR import visibility propagation — `src/compiler/20.hir/hir_lowering/_Items/module_import_registration.spl` | 919-935 |
| [R23] | HIR filename auto-public — `src/compiler/20.hir/hir_lowering/context_helpers.spl` | 241-248 |
| [R24] | Filename visibility helper — `src/compiler/00.common/visibility.spl` | 66-92 |
| [R25] | Visibility query public-set construction — `src/app/cli/_QueryVisibility/query_commands.spl` | 350-384; 576-590; 697-710 |
| [R26] | Query metadata Boolean upgrade — `src/compiler/90.tools/query_helpers.spl` | 96-111 |
| [R27] | Managed phase build command — `scripts/bootstrap/bootstrap-phase4-grouped.shs` | 247-274 |
| [R28] | Typed phase variant options — `src/app/bootstrap_builder/native_group_index_variant.spl` | 21-78 |
| [R29] | Provisional phase authority — `src/app/bootstrap_builder/native_group_provisional_authority.spl` | 184-191 |
| [R30] | Managed/legacy bootstrap handoff — `scripts/bootstrap/bootstrap-from-scratch.sh` | 5267-5279; 5767-5779; 5805-5829 |
| [R31] | Incremental object scope — `src/compiler/80.driver/driver_build/incremental.spl` | 553-579 |
| [R32] | Tree-sitter outline visibility — `src/compiler/10.frontend/treesitter/outline_decls.spl` | 119-140 |
| [R33] | Aspect pack I/O continuation — `src/compiler/99.loader/aspect_pack_io.spl` | 161-164 |
| [R34] | Richer scoped checker helpers — `src/compiler/35.semantics/visibility_checker.spl` | 130-243 |
| [R35] | Typed compile options — `src/compiler/00.common/driver_compile_options.spl` | 16-56 |
| [R36] | Hosted startup/runtime initialization order — `src/compiler/70.backend/backend/llvm_native_link_hosted_support.spl` | 155-179 |

Related existing designs were consulted but are not treated as proof of the current implementation:

- [Aspect dynload lane plan, 2026-08-19](https://github.com/ormastes/simple/blob/97700b29e10675867891503f1e634b50a192356d/doc/03_plan/compiler/aspect_dynload/aspect_dynload_lane_plan_2026-08-19.md).
- [Aspect facets and SMF pack design, 2026-08-04](https://github.com/ormastes/simple/blob/97700b29e10675867891503f1e634b50a192356d/doc/05_design/language/aop/aspect_facet_dynload_smf_pack_design_2026-08-04.md). Its early implementation-status text is older than the current catalog code.
- [MDSOC visibility requester design](https://github.com/ormastes/simple/blob/97700b29e10675867891503f1e634b50a192356d/doc/05_design/app/mcp/mdsoc_visibility_requester_design.md).
- [Machine-readable AOP support matrix](https://github.com/ormastes/simple/blob/97700b29e10675867891503f1e634b50a192356d/src/compiler/85.mdsoc/aop_support_matrix.sdn). Advertised support needs the parser/matcher/backend parity tests in this plan.

### 15.2 External primary references

- **E01:** [LLVM XRay instrumentation](https://llvm.org/docs/XRay.html) — instrumentation, runtime control, and selective patching.
- **E02:** [Clang XRay attributes](https://clang.llvm.org/docs/AttributeReference.html#xray-always-instrument-xray-never-instrument-xray-log-args) — candidate and exclusion attributes.
- **E03:** [Clang command-line reference](https://clang.llvm.org/docs/ClangCommandLineReference.html) — XRay compile/link/instrumentation options; a flag's presence alone is not target acceptance.
- **E04:** [Official Language Server Protocol](https://microsoft.github.io/language-server-protocol/) and [protocol specification](https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/) — language-service integration and JSON-RPC. Also see the primary [semantic-token legend API](https://microsoft.github.io/monaco-editor/typedoc/interfaces/editor_editor_api.languages.SemanticTokensLegend.html).
- **E05:** [Java Language Specification, access control](https://docs.oracle.com/javase/specs/jls/se25/html/jls-6.html#jls-6.6) — the limited package-default analogy, not Simple's own visibility contract.

External references were checked on 2026-10-31. Design choices such as export promotion, TLS storage policy, profile defaults, and cache schemas are recommendations for Simple in this plan, not claims that LLVM or LSP supplies them automatically.

## 16. Final checklist

- [ ] No-modifier folder access and explicit-private are distinct and enforced.
- [ ] All-public declarations and directory-exported bindings are accurately shown by compiler/LSP/MCP and selected by AOP.
- [ ] Named-aspect grammar and shared selector matching are consistent.
- [ ] Existing aspect loading is connected to real XRay execution events on an admitted target.
- [ ] Folder logging is a dynloadable, bounded, thread-local debug concern with honest observed depth.
- [ ] Phase 3 enables the development debug option; phase 4 builds a statically-off release.
- [ ] Release debug activation is denied without disabling ordinary functional dynload.
- [ ] Metadata, caches, proofs, tests, and docs use the same semantics and profile identity.
- [ ] No `call`, getter/setter generation, parameter/return capture, or unrelated new AOP feature was added.

[R01]: https://github.com/ormastes/simple/blob/97700b29e10675867891503f1e634b50a192356d/src/runtime/runtime_native.c
[R02]: https://github.com/ormastes/simple/blob/97700b29e10675867891503f1e634b50a192356d/src/lib/common/aspect_pack.spl
[R03]: https://github.com/ormastes/simple/blob/97700b29e10675867891503f1e634b50a192356d/src/os/port/llvm/compiler_rt_cmake.cmake
[R04]: https://github.com/ormastes/simple/blob/97700b29e10675867891503f1e634b50a192356d/src/compiler/10.frontend/core/aop_predicate_parser.spl
[R05]: https://github.com/ormastes/simple/blob/97700b29e10675867891503f1e634b50a192356d/src/compiler/10.frontend/core/aop.spl
[R06]: https://github.com/ormastes/simple/blob/97700b29e10675867891503f1e634b50a192356d/src/compiler/10.frontend/parser_types.spl
[R07]: https://github.com/ormastes/simple/blob/97700b29e10675867891503f1e634b50a192356d/src/compiler/10.frontend/core/aop_debug_log.spl
[R08]: https://github.com/ormastes/simple/blob/97700b29e10675867891503f1e634b50a192356d/src/compiler/10.frontend/core/_ParserDecls/enum_module_body.spl
[R09]: https://github.com/ormastes/simple/blob/97700b29e10675867891503f1e634b50a192356d/src/compiler/20.hir/hir_lowering/_Items/module_import_resolution.spl
[R10]: https://github.com/ormastes/simple/blob/97700b29e10675867891503f1e634b50a192356d/src/compiler/35.semantics/visibility_integration.spl
[R11]: https://github.com/ormastes/simple/blob/97700b29e10675867891503f1e634b50a192356d/src/compiler/00.common/dependency/visibility.spl
[R12]: https://github.com/ormastes/simple/blob/97700b29e10675867891503f1e634b50a192356d/src/app/cli/_QueryVisibility/feature_visibility.spl
[R13]: https://github.com/ormastes/simple/blob/97700b29e10675867891503f1e634b50a192356d/src/lib/nogc_sync_mut/lsp/lsp_handlers.spl
[R14]: https://github.com/ormastes/simple/blob/97700b29e10675867891503f1e634b50a192356d/src/app/io/_CliCompile/compile_targets.spl
[R15]: https://github.com/ormastes/simple/blob/97700b29e10675867891503f1e634b50a192356d/src/app/bootstrap_builder/native_group_phase2_authority.spl
[R16]: https://github.com/ormastes/simple/blob/97700b29e10675867891503f1e634b50a192356d/src/compiler/85.mdsoc/aop_cache/aop_group_keys.spl
[R17]: https://github.com/ormastes/simple/blob/97700b29e10675867891503f1e634b50a192356d/src/verification/visibility_export/src/VisibilityExport.lean
[R18]: https://github.com/ormastes/simple/blob/97700b29e10675867891503f1e634b50a192356d/src/compiler/10.frontend/core/_ParserDecls/bitfield_aop_arch_decls.spl
[R19]: https://github.com/ormastes/simple/blob/97700b29e10675867891503f1e634b50a192356d/src/compiler/80.driver/driver_pipeline_aop.spl
[R20]: https://github.com/ormastes/simple/blob/97700b29e10675867891503f1e634b50a192356d/src/compiler/50.mir/mir_aop_injection.spl
[R21]: https://github.com/ormastes/simple/blob/97700b29e10675867891503f1e634b50a192356d/src/compiler/20.hir/hir_lowering/_Items/module_declarations_bootstrap.spl
[R22]: https://github.com/ormastes/simple/blob/97700b29e10675867891503f1e634b50a192356d/src/compiler/20.hir/hir_lowering/_Items/module_import_registration.spl
[R23]: https://github.com/ormastes/simple/blob/97700b29e10675867891503f1e634b50a192356d/src/compiler/20.hir/hir_lowering/context_helpers.spl
[R24]: https://github.com/ormastes/simple/blob/97700b29e10675867891503f1e634b50a192356d/src/compiler/00.common/visibility.spl
[R25]: https://github.com/ormastes/simple/blob/97700b29e10675867891503f1e634b50a192356d/src/app/cli/_QueryVisibility/query_commands.spl
[R26]: https://github.com/ormastes/simple/blob/97700b29e10675867891503f1e634b50a192356d/src/compiler/90.tools/query_helpers.spl
[R27]: https://github.com/ormastes/simple/blob/97700b29e10675867891503f1e634b50a192356d/scripts/bootstrap/bootstrap-phase4-grouped.shs
[R28]: https://github.com/ormastes/simple/blob/97700b29e10675867891503f1e634b50a192356d/src/app/bootstrap_builder/native_group_index_variant.spl
[R29]: https://github.com/ormastes/simple/blob/97700b29e10675867891503f1e634b50a192356d/src/app/bootstrap_builder/native_group_provisional_authority.spl
[R30]: https://github.com/ormastes/simple/blob/97700b29e10675867891503f1e634b50a192356d/scripts/bootstrap/bootstrap-from-scratch.sh
[R31]: https://github.com/ormastes/simple/blob/97700b29e10675867891503f1e634b50a192356d/src/compiler/80.driver/driver_build/incremental.spl
[R32]: https://github.com/ormastes/simple/blob/97700b29e10675867891503f1e634b50a192356d/src/compiler/10.frontend/treesitter/outline_decls.spl
[R33]: https://github.com/ormastes/simple/blob/97700b29e10675867891503f1e634b50a192356d/src/compiler/99.loader/aspect_pack_io.spl
[R34]: https://github.com/ormastes/simple/blob/97700b29e10675867891503f1e634b50a192356d/src/compiler/35.semantics/visibility_checker.spl
[R35]: https://github.com/ormastes/simple/blob/97700b29e10675867891503f1e634b50a192356d/src/compiler/00.common/driver_compile_options.spl
[R36]: https://github.com/ormastes/simple/blob/97700b29e10675867891503f1e634b50a192356d/src/compiler/70.backend/backend/llvm_native_link_hosted_support.spl

[E01]: https://llvm.org/docs/XRay.html
[E02]: https://clang.llvm.org/docs/AttributeReference.html#xray-always-instrument-xray-never-instrument-xray-log-args
[E03]: https://clang.llvm.org/docs/ClangCommandLineReference.html
[E04]: https://microsoft.github.io/language-server-protocol/
[E05]: https://docs.oracle.com/javase/specs/jls/se25/html/jls-6.html#jls-6.6

<!-- Revision 1.1: local release-base source references; no external refresh. -->
[Q01]: https://github.com/ormastes/simple/blob/d9ff974b3c967579ab00b64ef7d03ae2424d8e4e/src/runtime/runtime_native.c
[Q02]: https://github.com/ormastes/simple/blob/d9ff974b3c967579ab00b64ef7d03ae2424d8e4e/src/compiler/70.backend/backend/llvm_native_link_hosted_support.spl
[Q03]: https://github.com/ormastes/simple/blob/d9ff974b3c967579ab00b64ef7d03ae2424d8e4e/src/lib/common/aspect_pack.spl
[Q04]: https://github.com/ormastes/simple/blob/d9ff974b3c967579ab00b64ef7d03ae2424d8e4e/src/compiler/10.frontend/core/aop_predicate_parser.spl
[Q05]: https://github.com/ormastes/simple/blob/d9ff974b3c967579ab00b64ef7d03ae2424d8e4e/src/compiler/10.frontend/core/_ParserDecls/bitfield_aop_arch_decls.spl
[Q06]: https://github.com/ormastes/simple/blob/d9ff974b3c967579ab00b64ef7d03ae2424d8e4e/src/compiler/10.frontend/core/aop.spl
[Q07]: https://github.com/ormastes/simple/blob/d9ff974b3c967579ab00b64ef7d03ae2424d8e4e/src/compiler/10.frontend/parser_types.spl
[Q08]: https://github.com/ormastes/simple/blob/d9ff974b3c967579ab00b64ef7d03ae2424d8e4e/src/compiler/10.frontend/core/_ParserDecls/enum_module_body.spl
[Q09]: https://github.com/ormastes/simple/blob/d9ff974b3c967579ab00b64ef7d03ae2424d8e4e/src/compiler/10.frontend/treesitter/outline_decls.spl
[Q10]: https://github.com/ormastes/simple/blob/d9ff974b3c967579ab00b64ef7d03ae2424d8e4e/src/compiler/20.hir/hir_lowering/context_helpers.spl
[Q11]: https://github.com/ormastes/simple/blob/d9ff974b3c967579ab00b64ef7d03ae2424d8e4e/src/compiler/20.hir/hir_lowering/_Items/module_declarations_bootstrap.spl
[Q12]: https://github.com/ormastes/simple/blob/d9ff974b3c967579ab00b64ef7d03ae2424d8e4e/src/compiler/20.hir/hir_lowering/_Items/module_import_registration.spl
[Q13]: https://github.com/ormastes/simple/blob/d9ff974b3c967579ab00b64ef7d03ae2424d8e4e/src/compiler/00.common/dependency/visibility.spl
[Q14]: https://github.com/ormastes/simple/blob/d9ff974b3c967579ab00b64ef7d03ae2424d8e4e/src/app/cli/_QueryVisibility/feature_visibility.spl
[Q15]: https://github.com/ormastes/simple/blob/d9ff974b3c967579ab00b64ef7d03ae2424d8e4e/src/lib/nogc_sync_mut/lsp/lsp_handlers.spl
[Q16]: https://github.com/ormastes/simple/blob/d9ff974b3c967579ab00b64ef7d03ae2424d8e4e/src/lib/nogc_sync_mut/lsp/lsp_query_command.spl
[Q17]: https://github.com/ormastes/simple/blob/d9ff974b3c967579ab00b64ef7d03ae2424d8e4e/src/app/bootstrap_builder/native_group_phase2_authority.spl
[Q18]: https://github.com/ormastes/simple/blob/d9ff974b3c967579ab00b64ef7d03ae2424d8e4e/src/app/bootstrap_builder/native_group_provisional_authority.spl
[Q19]: https://github.com/ormastes/simple/blob/d9ff974b3c967579ab00b64ef7d03ae2424d8e4e/src/app/bootstrap_builder/native_group_index_variant.spl
[Q20]: https://github.com/ormastes/simple/blob/d9ff974b3c967579ab00b64ef7d03ae2424d8e4e/src/app/io/_CliCompile/compile_targets.spl
[Q21]: https://github.com/ormastes/simple/blob/d9ff974b3c967579ab00b64ef7d03ae2424d8e4e/src/compiler/00.common/driver_compile_options.spl
[Q22]: https://github.com/ormastes/simple/blob/d9ff974b3c967579ab00b64ef7d03ae2424d8e4e/src/compiler/85.mdsoc/aop_cache/aop_group_keys.spl
[Q23]: https://github.com/ormastes/simple/blob/d9ff974b3c967579ab00b64ef7d03ae2424d8e4e/src/compiler/80.driver/driver_build/incremental.spl
