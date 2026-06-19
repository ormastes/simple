# Calc Formula Display Functions NFR

- CALC-FUNC-NFR-001: Display-safe formula functions must avoid the f64 return
  path so runner-verifiable behavior is not affected by the current f64 backend
  blocker.
- CALC-FUNC-NFR-002: Display-safe function evaluation must remain pure and must
  not use filesystem, shell, browser, network, or GUI APIs.
- CALC-FUNC-NFR-003: Unsupported or malformed display function calls must fail
  closed to an empty display string instead of throwing or recursing without a
  depth bound.
