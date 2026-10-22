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

The gate also runs when the native build tool considers the target up to date. P11 showed that a compiler launcher is not invoked for an undeclared policy-only edit; P12 showed the additional object-dependency mechanism for the tested CMake/Ninja case. The production adapter therefore needs an always-run top-level gate and dependency-stamp integration. [Local evidence](evidence/probe_results.md) [S08](05_sources_and_evidence.md#s08) [S11](05_sources_and_evidence.md#s11)

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
