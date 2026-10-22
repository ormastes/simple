# Simple / Clang header-cache final plan

**Date:** 2026-09-25  
**Deliverable:** Design, integration plan, SDN authoring example, native counterexample probes, and implementation acceptance requirements.  
**Status:** Proposal, not deployed code. The local probes are real; the proposed Simple cache/provider, SDN policy evaluator, and CI integration were not executed.

## Executive decision

**Unexpected macro/context variation is an error by default. Approved variation creates a separate valid cache context. A reviewed macro/file exception selects complete-context caching or no semantic reuse; it never means “ignore this input in the key”.**

Keep permission, cache validity and binary/semantic compatibility as separate decisions. A registered file is an authorized source of input, not an input whose content can be skipped. A normal content edit usually invalidates a resource; a violation means unapproved variation or an incompatible policy contract.

| Situation | Final treatment |
|---|---|
| Extra/changed/removed project predefinition outside the admitted profile | Error, on both cold and warm builds. |
| Declared varying macro uses an approved definition state/value | Accept permission; select/build the matching context. |
| Registered generated configuration file changes | Validate permitted exports/values; use current producer output and rekey dependents. |
| Scoped macro/file exception with `complex` | Allow its specified variation while retaining complete supported context. |
| Scoped exception with `none` | Process fresh; prohibit enclosing semantic-cache shortcuts that hide the input. |
| Unknown preprocessor or semantic state | Conservative complete boundary, explicit no-cache fallback, or error—not guessed reuse. |
| Valid object caches disagree on a governed public ABI profile | Reject compatibility independently of cache correctness. |

## Recommended implementation architecture

```text
CMake configuration + optional File API metadata
                       |
           Ninja native graph (initially)
                       |
        Simple launcher / top-level policy gate
                       |
           SDN profiles and action manifests
                       |
             scheduler + resource service
                       |
       pinned Clang group / mid-scheduler
                       |
       compile threads + mutable resource indexes
                       |
       private frontend/LLVM state per compilation
                       |
   verified native PCH/PCM/BMI + object resources
```

Use isolated Clang processes as the first correct reference. Qualify the persistent library/group provider afterward. Clang's existing `clang-cpp` library is a useful substrate, but dynamic linkage is not itself a speed guarantee. Keep a static warm-provider benchmark and exact toolchain pinning. [Integration report](03_clang_cmake_ninja_integration.md)

Native control/metadata/protocol stays **SDN**. Payloads and optional local ring structures are binary. CMake JSON and workflow YAML stay at their external-tool boundaries. Do not reimplement CMake's language or treat File API/compilation-database metadata as the full executable graph.

## Reports

| File | Purpose |
|---|---|
| [FINAL_REPORT.md](FINAL_REPORT.md) | Combined new reports, source register and observed probe summary. |
| [01_macro_header_policy.md](01_macro_header_policy.md) | Strict fixed/variant policy, file registration, scoped exceptions, SDN and diagnostics. |
| [02_cache_engine_resource_sharing.md](02_cache_engine_resource_sharing.md) | Complete keys, negative dependencies, PP transitions, native resource boundaries and sharing. |
| [03_clang_cmake_ninja_integration.md](03_clang_cmake_ninja_integration.md) | Library provider, CMake launcher/stamps, File API roles, and optional full Ninja execution. |
| [04_ci_tests_implementation.md](04_ci_tests_implementation.md) | Local/GitHub gates, retry policy, repository rules, H0–H9 packages and 56 planned acceptance tests. |
| [05_sources_and_evidence.md](05_sources_and_evidence.md) | Primary sources, actual test environment, executed probes and evidence limitations. |
| [examples/header_policy.sdn.example](examples/header_policy.sdn.example) | Illustrative policy authoring shape; not parser-validated. |
| [examples/policy_recipes.md](examples/policy_recipes.md) | Concrete per-macro/per-file choices and expected outcomes. |
| [evidence/probe_results.md](evidence/probe_results.md) | Actual outcomes of 12 local native counterexample probes. |
| [evidence/run_probes.py](evidence/run_probes.py) | Reproduction script with fixture construction and temporary-work cleanup. |
| [prior_plan/README.md](prior_plan/README.md) | Unmodified earlier four-report build-platform plan and provenance. |

## Most important findings

The tested Clang distinguishes macro definition states, ordered `-D/-U`, absent-to-present headers, repeated X-macro includes, entering pragma state, preceding semantic declarations and builtin counter state. Therefore a header key composed only of its filename and known expanded macros is insufficient. The raw evidence and fixture code are bundled. [Local results](evidence/probe_results.md)

The CMake/Ninja probe also showed that a compiler launcher did not run after an undeclared policy-only change. Declaring the policy as an object prerequisite caused recompilation. The final design includes both an always-run policy gate and native invalidation bridges; just disabling the cache inside the launcher is not enough. [Integration findings](03_clang_cmake_ninja_integration.md#7-crucial-gap-ninja-may-never-call-the-launcher)

## Relationship to the earlier session plan

This extension preserves the earlier coupled-code monorepo, optional pinned examples/submodules, short-lived work/release branches, typed dependency graph, exact tools, SDN control, grouped processes, mutable startup caches, bounded isolated retries and complete CI receipts. It refines the header/preprocessor correctness contract and the CMake/Clang adapter. Where earlier prose suggested weaker header keys or a complete File API execution graph, the new reports are authoritative design corrections.

No current repository implementation status is inferred from these proposals. The copied baseline has its own dated audit; this extension did not repeat that audit. No repository, hook or GitHub setting was modified.

## Reading order and first milestone

Read the policy, then cache-engine constraints, then integration. Implement H0–H4 first: a reviewed SDN contract, complete isolated invocation capture, strict evaluation, correct cache admission, and a native launcher/policy-stamp bridge. Native PCH/module resource reuse and qualified grouped execution follow. General arbitrary-header token/AST replay and a full Ninja replacement are later optional work.

The fast-feedback goal remains **P95 below one minute for eligible warm ordinary changes**, not a measured result from this report and not permission to skip required evidence.
