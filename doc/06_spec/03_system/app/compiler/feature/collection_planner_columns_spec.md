# Typed collection column acceptance subcases

Status: **authored, not generated or runtime verified** (2026-10-03).
Executable: `test/03_system/app/compiler/feature/collection_planner_columns_spec.spl`.
Requirement: REQ-001 in `doc/02_requirements/feature/collection_planner.md`.
Parent acceptance inventory: `doc/03_plan/sys_test/collection_planner.md`,
CP-001-A/B/C. These seven subcases use the real synchronous TypedSeries,
Series and DataFrame APIs; they do not close the three parent cases.

| Subcase | Fixture and observable oracle |
|---|---|
| CP-001-A-map | Values `[-7,777,12]`, missing middle; actual callback panics on 777 and otherwise multiplies by three. Result `[-21,777,36]`, unchanged mask/name, masked `get` absent. This proves callback exclusion for the missing row, not exact invocation count for present rows. |
| CP-001-A-roundtrip | Typed i64 to dynamic Series to DataFrame lookup to typed column. Present `9007199254740993`, `-9007199254740993`, zero survive exactly; the third row remains missing. Both signed wide values distinguish integer storage from lossy f64 conversion. |
| CP-001-B-all-missing | Three nonempty rows all masked; actual predicate panics on every invocation. `any_present=false`, `all_present=true`, `filter_present` empty establish zero predicate invocations and vacuous semantics. |
| CP-001-C-index | Two-row column rejects -1 and length=2; valid indices 0 and 1 still return -5 and 8. |
| CP-001-C-constructor | Two values reject masks of lengths 1 and 3 independently. |
| CP-001-C-read-transform | Direct construction bypasses the constructor with two poisoned values and one mask bit. Read, map, filter, present filter, any/all and dynamic conversion must each return an error. Panic callbacks ensure shape validation precedes invocation. |
| CP-001-C-dtype | f64-as-i64 and i64-as-f64 reject; changing the outer Series dtype to the desired type must still reject incompatible NDArray backing storage. |

Visible flows reuse `prepare typed collection fixtures` and `compare results
and operation counts`. The only invocation-count guarantee established by the
callback traps is zero on excluded rows or rejected malformed columns. The
tests contain no fake execution receipts, mocked collection implementation,
or source-text oracle. Panic callbacks are actual functions passed into the
production methods and make accidental invocation observable.

## Outstanding parent acceptance

- CP-001-A: exact once-per-present callback count and callback order remain
  uninstrumented; only the synchronous API is exercised.
- CP-001-B: NaN non-match, signed-zero equality, stable numeric join duplicate
  policies and cross-engine behavior remain open; all-missing column queries
  alone cannot prove these.
- CP-001-C: current production APIs return `DfError.ShapeMismatch` for dtype,
  mask and index failures. These assertions require rejection without claiming
  distinct dtype/index diagnostics. Distinct error variants remain open.
- No admitted self-hosted runner has executed these scenarios. They are
  test-first authored contracts, not observed RED/GREEN; no source was changed
  in this increment. Existing implementation may already satisfy a subcase.
- Generated-manual admission remains open. Once an admitted runner/docgen is
  available, execute the spec, retain runtime/source/backend identity and
  assertion results, then regenerate this companion through SPipe docgen.

No numeric-join, five-engine parity, CollectionPlan extraction/lowering,
selected-algorithm execution or performance acceptance is inferred from these
column scenarios. The full REQ-001–011 objective remains unchanged.
