<!-- codex-research -->
# Domain Research: SimpleOS Desktop Core Formal Verification

**Date:** 2026-04-18  
**Scope:** Compare how high-reliability operating systems and adjacent systems actually use formal verification, and derive a realistic strategy for SimpleOS.

## Executive Summary

The external evidence is consistent:

- **seL4** is the strongest public benchmark for machine-checked kernel assurance
- **CertiKOS** is the strongest public benchmark for compositional verified kernel research
- **INTEGRITY-178B** is important as a certification/formal-methods comparison point, but its proof chain is not public and not source-connected in the way seL4 is
- **FreeRTOS** and **Zephyr** show that partial/component-level formal methods are common and useful, even when full-kernel proofs are absent

Conclusion for SimpleOS:

- use **seL4** as the benchmark for proof discipline and assumptions handling
- use **CertiKOS** as the benchmark for compositional proof layering
- treat **INTEGRITY-178B** as evidence that certification-grade formal methods matter in practice, while avoiding any “same level as INTEGRITY” claim
- follow **FreeRTOS/Zephyr** in using bounded proofs where whole-system proof is not yet realistic

## Benchmark 1: seL4

Primary sources:

- seL4 Fact Sheet: <https://sel4.systems/About/fact-sheet.html>
- seL4 Proofs: <https://sel4.systems/Verification/proofs.html>
- seL4 Assumptions: <https://sel4.systems/Verification/assumptions.html>

### What seL4 proves publicly

seL4 states publicly that its inspectable proof stack covers:

- functional correctness
- binary correctness in supported configurations
- security properties including:
  - integrity
  - confidentiality
  - availability

The seL4 site also emphasizes:

- proof maintenance over time
- no code change without proof validation
- explicit documentation of proof assumptions

### What seL4 does that SimpleOS should copy

1. **Explicit assumption ledger**
   - boot code, DMA, hardware-management, side-channel, and hardware assumptions are named explicitly

2. **Property-specific claim discipline**
   - seL4 distinguishes which properties hold on which configurations

3. **Static system-configuration correctness**
   - the proof stack includes a mechanism for correct system initialization and access-control configuration, not just kernel-code reasoning

### What seL4 implies for SimpleOS

SimpleOS should not claim formal verification without:

- named proof targets
- named assumptions
- named unsupported configurations
- a clear split between proved kernel facts and merely tested desktop behavior

## Benchmark 2: CertiKOS and Real-Time CertiKOS

Primary sources:

- CertiKOS PLDI page: <https://flint.cs.yale.edu/certikos/publications/security.html>
- Real-Time CertiKOS dissertation page: <https://flint.cs.yale.edu/certikos/publications/liu-thesis.html>

### What CertiKOS contributes

CertiKOS demonstrates:

- compositional verification of an OS kernel
- proof across both C and assembly
- proof preservation across abstraction layers

Real-Time CertiKOS adds:

- verified timer interrupt handling
- verified scheduler behavior
- temporal isolation reasoning

### What SimpleOS should learn from CertiKOS

1. **Prove seams, not slogans**
   - trap entry, scheduler semantics, and isolation contracts are the right proof units

2. **Scheduler claims must be specific**
   - if SimpleOS later claims desktop responsiveness, watchdog isolation, or service fairness, those claims need explicit scheduler properties and not just smoke tests

3. **Compositional layering matters**
   - kernel-core proofs should be separable from desktop-session constraints

## Benchmark 3: INTEGRITY-178B

Primary sources:

- Green Hills EAL6+/High Robustness announcement: <https://www.ghs.com/news/20081117_integrity_EAL6plus_security.html>
- Green Hills security-critical page: <https://www.ghs.com/products/safety_critical/integrity_178_security.html>
- seL4 comparison page: <https://sel4.systems/About/comparison.html>

### What is useful here

Green Hills positions INTEGRITY-178B as using:

- formal model and proof
- formal specifications
- certification-oriented evidence

### Critical caveat

seL4’s comparison page states that the INTEGRITY proof is:

- not public
- not broadly current across architectures/versions
- not formally connected to source code in the same way as seL4

### What SimpleOS should learn

- certification-oriented formal methods are meaningful in high-reliability systems
- but SimpleOS should benchmark itself against **public, inspectable proof artifacts**, not marketing-level equivalence claims

## Benchmark 4: FreeRTOS and Zephyr

Primary sources:

- AWS announcement mentioning CBMC-based memory-safety validation: <https://aws.amazon.com/about-aws/whats-new/2020/11/freertos-includes-iot-aws-libraries-optimized-memory-usage-modularity/>
- CBMC starter kit tutorial using FreeRTOS kernel proofs: <https://model-checking.github.io/cbmc-starter-kit/tutorial/index.html>
- Zephyr memory-management verification research:
  - <https://arxiv.org/abs/2309.09997>
  - <https://link.springer.com/chapter/10.1007/978-3-030-25543-5_29>

### What these systems show

- full public end-to-end kernel proof is unusual
- partial verification is common and still valuable
- bounded model checking and component proofs are practical for:
  - memory management
  - IPC
  - safety-critical library/kernel routines

### What SimpleOS should copy

- prove the highest-risk pure components first
- keep proofs in CI/automation where possible
- combine proofs with tests instead of pretending that tests are proofs

## Domain Conclusions For SimpleOS

### Recommended external posture

Allowed future claim style:

- “SimpleOS has bounded formal verification for defined kernel-core properties, with constrained desktop-session contracts and explicit assumptions.”

Disallowed claim style:

- “SimpleOS is a fully formally verified desktop OS”
- “SimpleOS matches seL4 assurance”
- “QEMU pass equals formal verification”

### Recommended proof strategy

1. **Kernel first**
   - trap/syscall
   - privilege state
   - capability/grant authorization
   - scheduler/task lifecycle
   - VM isolation requirements

2. **Desktop as constrained contract**
   - ownership
   - focus uniqueness
   - crash containment
   - launcher/session provenance
   - marker-based system evidence

3. **Assumption-first reporting**
   - every proof report must list what remains assumed

4. **Staged assurance taxonomy**
   - `proved`
   - `model-checked`
   - `spec-checked`
   - `system-tested`
   - `assumed`
