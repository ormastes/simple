# Bug: SdnValue cross-module variant dispatch fails in interpreter

**ID:** sdn_cross_module_variant_dispatch_2026-06-26
**Severity:** P2 (test blocker)
**Status:** Open

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

## NOT REPRODUCIBLE 2026-08-17 — appears FIXED BY CONTENT
Two measurements, seed binary `bin/release/x86_64-unknown-linux-gnu/simple`,
`--no-session-daemon`, exit code read directly:
1. `test/01_unit/lib/common/roundtrip_spec.spl` (the cited spec, imports
   `std.common.sdn.parser.{parse}` + `std.common.sdn.value.{SdnValue}` from a
   different module) — `6 examples, 0 failures`, `executed=6 passed=6 failed=0`, rc=0.
2. A targeted throwaway probe calling the method the doc names, on a document that
   contains primitive values:
   `match parse("name: \"x\"\ncount: 3\n") -> case Ok(v): v.type_name()`
   printed `type_name=dict` and passed (rc=0). No `unknown variant or method`.
Cross-module method dispatch on a parsed `SdnValue` therefore works today.
Status: recommend CLOSED-not-reproducible; reopen with a fresh failing snippet if
seen again.
