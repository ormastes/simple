# Collection plan selection: authored acceptance companion

Source: `test/01_unit/compiler/mir_opt/collection_plan_selection_spec.spl`.
This companion is not generated and has no runtime PASS evidence.

Existing scenarios exercise collection/attribute/policy validation, semantic
gates, contradictory size bounds, unknown cost facts, profile/collision advice,
critical worst-case policy, explicit attributes and alternative fallback.

## Memory admission scenarios

The test-first memory cases add unknown-budget rejection across policies and
attributes; invalid negative facts; unknown per-candidate bounds; explicit and
automatic selection; zero/exact/one-byte-over boundaries; profile preferences;
fitting Ordered fallback; rejection when every useful candidate exceeds the
cap; and maximum i64 values without arithmetic overflow.

Fixtures supply independent upper bounds on peak extra live bytes for the
candidate above Original. -1 means unknown and values below -1 are invalid.
These are inputs to the real production selector, not measurements of concrete
container allocations. Existing non-memory fixtures now supply these bounds
explicitly so their earlier semantic and policy assertions remain meaningful.

The memory regression tests were committed as `0131dfae5bf` before selector
implementation `69043e3fd64` in the isolated memory lane. No executable RED or
GREEN was obtained. Compiler cost production, actual lowering and runtime
memory/NFR evidence remain open; authored tests do not complete REQ-009.
