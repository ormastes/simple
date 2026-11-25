# A2UI Core Protocol & Express-SDN Frontend Manual

**Source Spec:** `test/01_unit/lib/common/ui/a2ui/a2ui_core_spec.spl`  
**Requirements:** `REQ-A2UI-001`, `REQ-A2UI-002`, `REQ-A2UI-003`, `REQ-A2UI-004`, `REQ-A2UI-005`

## Primary Scenarios

1. **Pinned Express.g4 Import & Strict SDN Output (`REQ-A2UI-001`)**
   - Import `Express.g4` rules into `A2uiGrammarModel` and serialize with unique rule keys.
   - Verify the emitted grammar SDN passes `sdn_parse_strict_v1`.
   - Reject unsupported `@members` directives with exact line numbers.

2. **Express Constructor Parsing on Shared Scalar VM (`REQ-A2UI-001`)**
   - Distinguish `_` omission (`A2uiArgPresence.Omitted`) from explicit `null` (`A2uiValue.Null`).
   - Reject trailing tokens and unsupported `@index()` expressions.

3. **Bounded Strict JSON Admission (`REQ-A2UI-003`)**
   - Reject nesting exceeding `max_depth` before recursive descent.
   - Reject duplicate decoded object keys and byte/token budget overruns.

4. **Complete Replacement & Qualified Handles (`REQ-A2UI-004`, `REQ-A2UI-005`)**
   - Encode and decode reversible `A2uiQualifiedHandle` identities across owner/surface/generation/component boundaries.
   - Confirm `UpdateComponents` replaces definitions completely and clears omitted properties such as `variant`.
