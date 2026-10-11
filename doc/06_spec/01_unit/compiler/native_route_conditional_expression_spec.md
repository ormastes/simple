# Native route conditional expression control

Host-authored scenario inventory; not admitted SPipe docgen or full cache-route verification.
Source: [native_route_conditional_expression_spec.spl](../../../../test/01_unit/compiler/native_route_conditional_expression_spec.spl).

| Scenario | Observable assertion |
| --- | --- |
| Legacy version 3 | One selected legacy module; distinct change is not selected |
| Current version 4 | One supplied private change |
| Future version 5 | Both supplied changes retain their order |
| Empty current hint | Result length is zero |

Frozen mixed-layout source failed construction before executing any example.
The corrected single-line source constructed 44 modules with zero failures and
ran once: **4 examples, 0 failures**, native exit 0. Assertions inspect actual
array lengths and contents. The helper isolates conditional construction and
branch selection; it does not invoke the complete production cache route.
See [dated construction report](../../../09_report/phase2_package_route_conditional_parse_2026-10-11.md).
Canonical Stage 2 remains unqualified; its three-attempt cap is exhausted.

The production layout was independently repaired in release commit
`a7c39dc8f5d` with a complete block-form conditional. This retained single-line
control records historical construction evidence; the obsolete production
hunk was removed from PR2968, and no current-owner runtime PASS is implied.
