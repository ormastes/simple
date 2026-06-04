# SimpleOS Desktop Core Formal Verification — NFR Options

**Feature:** `simpleos_desktop_core_formal_verification`  
**Date:** 2026-04-18  
**Status:** Options  
**Related:** [Feature Options](../feature/simpleos_desktop_core_formal_verification_options.md)

## Option A — Deep-Proof-First NFRs

**Description:** Require early proof depth approaching seL4-style expectations.

**Pros**

- strongest long-term assurance ambition
- drives rigorous proof decomposition from the start

**Cons**

- unrealistic for the current milestone
- blocked by current verifier/tooling gaps and broad OS scope

**Effort:** `XL`

## Option B — Staged Assurance Matrix

**Description:** Require all evidence to be labeled explicitly as `proved`, `model-checked`, `spec-checked`, `system-tested`, or `assumed`, with a mandatory assumption ledger.

**Pros**

- prevents over-claiming
- fits the current repo and user request
- scales cleanly into deeper future proof phases

**Cons**

- more process/documentation overhead
- requires disciplined report language

**Effort:** `M`

## Option C — Test-Dominant Assurance

**Description:** Prefer system tests and runtime checks, with only opportunistic formal work.

**Pros**

- lowest implementation friction

**Cons**

- too weak for a serious formal-verification program
- conflates strong test evidence with proof evidence

**Effort:** `S`

## Recommended Selection

**Selected:** Option B — Staged Assurance Matrix

Reason:

- it preserves truthfulness while still enabling meaningful bounded proof work
