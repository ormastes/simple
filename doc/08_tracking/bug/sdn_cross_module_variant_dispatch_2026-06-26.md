# Bug: SdnValue cross-module variant dispatch fails in interpreter

**ID:** sdn_cross_module_variant_dispatch_2026-06-26
**Severity:** P2 (test blocker)
**Status:** CLOSED (2026-09-12) — not reproducible on seed sha256 `3d120a6f`

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

## Re-check 2026-09-12 (BUGFIX-5)

Binary: `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple`
(Rust bootstrap seed, sha256 `3d120a6f`), worktree `/home/yoon/dev/simple-bugfix-5`
at base `89c5e3f865d`.

Cross-module probe (`bin/simple run`), a document whose Dict holds exactly the
primitive variants the record says trigger the failure (String, Int, Float,
Bool), with the calls the record names — `type_name()`, `is_dict()`, `get()`,
`as_str()`:

```
type_name=dict
is_dict=true
x.as_str=hello
x.type_name=string
```

No `unknown variant or method 'String' on enum SdnValue`. The affected spec is
green too, and it is not vacuous — it round-trips Int/String/Bool/Null through
`parse` and matches on `SdnValue.Int` / `.String` / `.Bool` / `.Null` in a
module other than `std.sdn.value`:

```
$ bin/simple test test/01_unit/lib/common/roundtrip_spec.spl --no-session-daemon
SPEC FILE VERDICT: test/01_unit/lib/common/roundtrip_spec.spl outcome=OK declared>=6 executed=6 passed=6 failed=0 skipped=0 dropped=0
```

Record said "5/6 tests fail"; now 6/6 pass. No code change made. Closing.

- Status: CLOSED (2026-09-12) — not reproducible on seed sha256 3d120a6f, 0ce26e5c97a, spec test/01_unit/lib/common/roundtrip_spec.spl
