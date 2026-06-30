# SimpleOS Desktop Core Formal Verification — Feature Options

**Feature:** `simpleos_desktop_core_formal_verification`  
**Date:** 2026-04-18  
**Status:** Options  
**Related:** [Local Research](../../01_research/local/simpleos_desktop_core_formal_verification.md), [Domain Research](../../01_research/domain/simpleos_desktop_core_formal_verification.md)

## Option A — Full Desktop Formal-Proof Claim

**Description:** Attempt to define and prove the whole desktop core, including compositor/session behavior, as a formal-verification milestone.

**Pros**

- strongest headline
- pushes proof work into the GUI/session layer early

**Cons**

- not supported by current repo state
- mixes pure kernel seams with highly stateful GUI/device behavior
- likely to force over-claiming or weak proof substitutes

**Effort:** `XL` (12+ files plus tool and harness work)

## Option B — Bounded Kernel Proof + Constrained Desktop Contract

**Description:** Formally specify and prove kernel-core invariants, and define a constrained desktop contract backed by specs and system evidence.

**Pros**

- matches current repo capabilities
- aligns with seL4/CertiKOS discipline on explicit assumptions and narrow claims
- provides a credible path for later deeper proofs

**Cons**

- does not justify a “fully verified desktop OS” claim
- requires careful documentation to separate proof from test evidence

**Effort:** `M` (8-10 files plus one seed OS spec)

## Option C — Safety Case Only

**Description:** Skip formal-proof scoping and produce only tests, runtime checks, and desktop/QEMU validation.

**Pros**

- fastest to deliver
- minimal verifier/tooling dependency

**Cons**

- loses the opportunity to use the existing Lean/contract infrastructure
- does not answer the request for formal verification in a meaningful way

**Effort:** `S` (4-6 files)

## Recommended Selection

**Selected:** Option B — Bounded Kernel Proof + Constrained Desktop Contract

Reason:

- it is the strongest option that remains honest relative to current SimpleOS and repo-local verification maturity
