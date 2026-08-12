<!-- codex-research -->
# Domain Research: Mission-Critical Infrastructure Hardening V2

Date: 2026-08-11

## Assurance lessons

- FAA AC 20-115D recognizes DO-178C and supplements such as DO-333; a project must apply the selected means consistently rather than promote partial evidence into a stronger assurance claim: https://www.faa.gov/airports/resources/advisory_circulars/index.cfm/go/document.information/documentNumber/20-115D
- seL4 publishes explicit proof scope and assumptions and separates functional correctness, integrity, confidentiality, availability, and initialization proofs. This supports platform/version-specific certification manifests rather than an unqualified global label: https://sel4.systems/Verification/proofs.html
- NIST SSDF requires secure-development practices to be integrated through the lifecycle and calls for component integrity verification: https://csrc.nist.gov/pubs/sp/800/218/final
- Reproducible Builds treats deterministic source-to-binary reconstruction and recorded environments as supply-chain evidence, while diverse double compilation addresses trusting-trust risk: https://reproducible-builds.org/ and https://dwheeler.com/trusting-trust/
- CompCert frames its high-assurance contract as semantic preservation from accepted source to generated assembly and permits fail-closed refusal for unsupported programs: https://compcert.org/man/manual001.html

## Graphics and allocation lessons

- Vulkan SC emphasizes deterministic behavior, offline preparation, bounded resource use, fixed/static pools, and explicit synchronization/resource control: https://www.khronos.org/vulkansc/
- Vulkan allocator callbacks are synchronous with the provoking thread, allocator state must outlive the object, and destruction must use a compatible allocator. Allocation policy is therefore part of object-lifetime correctness, not an interchangeable optimization: https://github.khronos.org/Vulkan-Site/spec/latest/chapters/memory.html
- NASA F Prime normally prohibits runtime dynamic allocation in flight operation and allocates during initialization: https://fprime.jpl.nasa.gov/latest/docs/user-manual/framework/memory-management/
- NASA/JPL safety guidance likewise discourages dynamic allocation, especially after initialization: https://ntrs.nasa.gov/api/citations/20080015887/downloads/20080015887.pdf

## Implications for Simple

1. Mission-critical claims must be configuration-, platform-, artifact-, and assumption-specific.
2. The production compiler must have exact lineage, reproducible inputs, executed semantic oracles, and eventually diverse or formally supported translation evidence.
3. Active-frame and critical-runtime allocation should use planned admission into fixed/preallocated capacity; growth belongs to initialization or controlled generation transitions.
4. A relaxed policy can remain safe only when it is narrower than the strict default: named/versioned, forbidden in critical contexts, bounded by hard quotas, observable, fault-injected, and deterministic on exhaustion.
5. Relaxed atomics are not synonymous with relaxed allocation and must never publish ownership/lifetime state without a separate memory-model proof.
