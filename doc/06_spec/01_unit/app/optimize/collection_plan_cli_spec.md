# Collection plan explanation scenarios

Executable source: `test/01_unit/app/optimize/collection_plan_cli_spec.spl`.
Requirement: REQ-PSC-006. Manually authored companion; generated-manual
verification and admitted self-hosted execution are pending.

Explain an attributed container using its parser-issued site. The explanation
must distinguish a proved default constructor from a factory whose returned
container may carry a different policy.

| Scenario | Expected outcome |
|---|---|
| Typed `Factory.new()` or `instance.new()` initializer | Initializer remains unproved; its method name is insufficient evidence. |
| Matching `AdaptiveTextSet.new()` with no arguments | Recognized as the default adaptive constructor. |
| Source fixture with auto and forced linear attributes | Four distinct sites retain their declared algorithms. |
| Identical declarations in separate nested functions | Site identities include the respective lexical owners. |
| Attributed class field defaults | Set and map fields retain owner and algorithm identity. |
| Forced ordered attribute on a typed factory | Explanation reports the explicit algorithm and unproved initializer. |
| Requested default site | Explanation selects the requested site and discloses disconnected typed MIR. |
| Generic auto map | Explanation includes key-order guards and unsupported-key demotion. |
| Admitted collision-heavy profile | Explanation selects ordered storage and reports measured probe/collision counts. |

The Phase 1 diagnostic passes the first eight scenarios. The final scenario
still reports collision p95 as 100 instead of 40. See
`doc/03_plan/evidence/seven_plans/windows/item7_initializer_explanation_2026-09-29.md`.
This manual does not constitute a production PASS.
