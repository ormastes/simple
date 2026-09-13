# Bug: SdnValue cross-module variant dispatch fails in interpreter

## Closed 2026-09-13 — cross-module SdnValue method dispatch works on primitive-bearing documents
- **measured** (Windows Rust seed v1.0.0-rc.1, `bin/simple run`, caller module != `std.sdn.value`): `parse("x: hello").unwrap().type_name()` printed `type=dict` and `.as_dict()` succeeded (`ok-as_dict`) — a Dict containing a String primitive, exactly the shape this entry says fails.
- **measured**: no `unknown variant or method 'String' on enum SdnValue` error appeared.
- **inferred**: the API also changed — `parse()` now returns a `Result`, so the entry's literal snippet fails with `Function 'Result.type_name' not found`; that is an API move, not the dispatch defect.
- **inferred**: `test/01_unit/lib/common/roundtrip_spec.spl` was not re-run; `bin/simple test` is broken on this Windows host.

**ID:** sdn_cross_module_variant_dispatch_2026-06-26
**Severity:** P2 (test blocker)
**Status:** CLOSED 2026-09-13 (see Closed section above)

## Symptom

In the interpreter (bin/simple run), calling ANY method on a `SdnValue` returned
by `std.sdn.parser.parse()` fails with "unknown variant or method 'X' on enum
SdnValue" when the parsed document contains primitive values (Int, Float, String,
Bool). The error fires even when calling intra-module methods like `type_name()`,
`as_dict()`, `as_str()`, etc.

Affected call patterns (from a different module than `std.sdn.value`):
```spl
val v = parse("x: hello")  # Dict with String value
v.type_name()              # → semantic: unknown variant or method 'String' on enum SdnValue
v.as_dict()                # → same error
```

Calls that DO work: values where the Dict only contains Null or Array values.

## Root Cause (hypothesis)

The interpreter builds a per-object method dispatch table that includes the
RUNTIME VARIANT names of values transitively reachable from the object (e.g.,
all values inside a Dict). When `SdnValue` is defined in `std.sdn.value` but
the caller is in a different module, the interpreter cannot resolve variant
names (Int, String, Bool, Float) during dispatch, raising "unknown variant or
method 'X'".

Null and Array/Dict containers don't trigger this because Null has no payload
and container variants have their own identity in the registry.

## Affected Spec

`test/01_unit/lib/common/roundtrip_spec.spl` — 5/6 tests fail.

## Workaround

None available without a seed fix. The tests are left failing. Container-only
paths (block arrays with no primitive values surfaced) accidentally pass
because they avoid the problematic dispatch.

## Fix Required

Seed interpreter fix in `src/compiler_rust/`: the method lookup for cross-module
enum values must not walk contained-value variants to resolve dispatch. Intra-module
method calls on SdnValue should bypass the cross-module variant registry.
