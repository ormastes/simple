# Bug: `std.sdn.*` resolves to a STALE bundled stdlib copy (divergent SdnValue API)

**Date:** 2026-06-30
**Severity:** Medium — latent. Any code importing `std.sdn.value` / `std.sdn.parser`
silently gets the seed-bundled SDN module, whose `SdnValue` has a DIFFERENT,
older variant set (`bool`/`i32`/`f32`/`text`, no `Int`/`String`/`Float`/`Bool`).
A `match v: case SdnValue.Int(i)` then fails with "unknown variant or method
'Int' on enum SdnValue", even though the canonical `SdnValue` clearly has `Int`.
**Component:** module path resolution — `interpreter_module/path_resolution.rs`.

## Two divergent copies of the SDN stdlib

| Path | `SdnValue` variants | Reached by |
|------|--------------------|-----------|
| `src/lib/common/sdn/value.spl` (canonical, live) | `Null Bool Int Float String Array Dict Table(headers:,rows:)` | `use std.common.sdn.value` |
| `src/compiler_rust/lib/std/src/sdn/value.spl` (seed-bundled, STALE) | `Null bool i32 f32 text Array Dict Table(pos 3-tuple)` | `use std.sdn.value` |

`path_resolution.rs:666` lists `src/compiler_rust/lib/std/src` ahead of the
other std roots, and there is NO `std.*` root mapping to `src/lib/common`, so
`std.sdn.*` ONLY ever finds the bundled stale copy. No active `src/lib` /
`src/app` code uses the bundled `i32` API; 10+ files use the canonical `Int`
API (imported via `std.common.sdn.*`).

## Reproducer

```simple
use std.sdn.value.{SdnValue}
fn main():
    print(SdnValue.i32(5))   # OK   — bundled-only variant resolves
    print(SdnValue.Int(5))   # FAIL — "unknown variant or method 'Int'"
```

## Workaround (LANDED)

`test/01_unit/lib/common/roundtrip_spec.spl` now imports the canonical path
`std.common.sdn.{parser,value}` instead of `std.sdn.*`. That is the correct path
for the live Int-API SDN module.

## Proper fix (not done — needs a design call)

The two SDN stdlibs have genuinely diverged (different value model). Either:
- reconcile / delete the stale bundled `src/compiler_rust/lib/std/src/sdn/*`
  if it is no longer needed for bootstrap, or
- make `std.sdn.*` resolve to the canonical `src/lib/common/sdn` for non-seed
  runs (resolver precedence), or
- formally deprecate `std.sdn.*` in favour of `std.common.sdn.*`.
Touching the bundled copy or resolver order risks the bootstrap path, so this is
deferred to a deliberate change.
