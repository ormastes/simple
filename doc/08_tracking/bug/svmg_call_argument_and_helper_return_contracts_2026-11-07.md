# SVM-G call arguments, helper returns and ascending range termination

Date: 2026-11-07
Status: implementation/spec and report source review approved; runtime verification pending.

## Source findings

1. A nested helper call can overwrite an earlier argument waiting in the shared callee parameter slots. Source inspection predicts `add(1, add(2, 3))` produces 7 rather than 6; this example has not been executed in this session.
2. A helper body ending in a known zero-word expression such as a print or loop can report successful lowering and attempt to store a return word that was never produced.
3. A positive signed loop increment can wrap at the maximum integer and continue an ascending range instead of terminating. The inclusive maximum-value singleton is a focused example; runtime behavior remains unverified.

## Repair

`src/compiler/70.backend/svmg_lowering.spl` stages arguments in call-site temporaries before assigning callee parameters, retaining source-order evaluation. It rejects known zero-word helper return tails and exits ascending signed ranges when a positive increment wraps. A helper-produced step is evaluated once per increment. This scope makes no new claim about negative-step or unsigned range semantics.

The repair preserves the previous expression-stack and numeric-assertion work landed in PR #7434. Its source owner at observed release `3362849eda19d05b6e9b4a3aa0782681da2e2471` is blob `0b01543a132b10e49c6e79e074a7d5580f634cc5`.

## Authored prevention coverage

Seven new parameterized cases in `test/01_unit/compiler/backend/svmg_lowering_spec.spl` cover earlier arguments across nested same-helper calls; transitive calls with single source-order side effects; zero-word helper tail rejection; nested conditional return values; single evaluation of an overflowing helper step; an inclusive maximum-value singleton; and positive increments that wrap or normally overshoot.

Astra approved the implementation/spec delta with no remaining P0/P1 findings. Approved raw SHA-256 values are source `C6BDF4C40891022295F4DF7E34D0FDC7654FD784D896564967762DF82D85748A` and spec `D67B10462B83A4468C84BB9E4E66E13BDD4E19CB359A39FBE4E1E42FD2DC63FC`.

## Verification boundary

The seven cases are authored but UNEXECUTED because an admitted self-hosted compiler is unavailable. Source review and static delimiter/whitespace checks do not establish runtime qualification. No verify PASS or all-bugs-complete claim is made. The user authorized source-complete landing after final Astra review with runtime verification pending.
