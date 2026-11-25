# Bug: `newtype` run-path + enforcement gaps
## Open 2026-09-16 — needs owner triage

## Triage 2026-11-25 (p2w4-ac lane, release/1.0.0)

Fresh probes on the pinned Rust seed (`bin/simple.exe` v1.0.0-rc.1, Windows,
`SIMPLE_LIB=src`; note the 2026-07-17 verification below used the
self-hosted binary, so seed-vs-self-hosted parity is not guaranteed):

- **Item #1, argument-position half — STILL REPRODUCES:** `takes_lba(Ppn(value: 5))`
  runs and prints `5`; no nominal-distinctness error on parameter passing.
- **Item #1, mixed-arithmetic half — NOW REJECTED:** `fn mix(a: Lba, b: Ppn): (a + b).value`
  fails semantic analysis with `SPL-UNIT-002: Lba + Ppn: distinct units never
  mix implicitly is not an approved unit operation`. The new unit system
  closes the arithmetic half of #1; every numeric `newtype` now also emits
  `SPL-UNIT-003` advising migration to `unit X: i64 as <suffix>`.
- **Item #2 (arithmetic erases wrapper) — still FIXED:** `(l + Lba(value:1)).value`
  prints `6`.
- **Item #3 (JIT cannot lower newtypes) — STILL REPRODUCES:** the same probe
  logs `HIR lowering error: Unsupported feature: cannot infer field type
  while lowering takes_lba: struct 'ANY' field 'value'` and falls back to the
  interpreter (message shape changed from `Unknown type: Lba`, same class).
- **Item #4 — not re-tested** (needs a genuine cross-module import lane).

Remaining work (nominal distinctness at call sites, JIT lowering of
newtypes) is compiler-wide and intersects the in-flight `unit` migration
(`SPL-UNIT-003`), i.e. owner-direction territory, not a bounded P2 fix.
Left OPEN with the refined per-item state above.

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Filed:** 2026-06-29
**Severity:** medium (feature immaturity; has disciplined workarounds)
**Found while:** building the custom-typed NVMe host/device emulator
(`examples/09_embedded/simpleos_nvme_fw/emu/`, "highly custom typed" requirement).

`newtype X = i64` is usable but several behaviours undercut its value as a domain
type. All reproduced this session on `bin/simple` (self-hosted), interp `run` path.

## 1. No type-safety enforcement (check AND run)
A function taking `Lba` accepts a `Ppn`, and mixed-newtype arithmetic is allowed —
both pass `check` ("All checks passed") and `run`:
```
newtype Lba = i64
newtype Ppn = i64
fn takes_lba(l: Lba) -> i64: l.value
fn mix(a: Lba, b: Ppn) -> i64: (a + b).value     # accepted
fn main(): print takes_lba(Ppn(value: 5))        # prints 5, no error
```
Expected: passing `Ppn` where `Lba` is required, and `Lba + Ppn`, should be type
errors (that is the entire point of a newtype). Today newtypes are documentation
only — no nominal distinctness is enforced.

## 2. Arithmetic on a newtype erases the wrapper (run)
`l + Lba(value: 1)` yields a bare `i64`, so a following `.value` fails with
`undefined field 'value' ... on i64`. Workaround: unwrap, compute in i64, rewrap
(`Lba(value: l.value + 1)`).

## 3. JIT cannot lower newtypes
Any module using a newtype logs `JIT compilation failed ... HIR lowering error:
Unknown type: Lba` and falls back to the interpreter unconditionally. Cross-module
import of a newtype additionally prints `[WARN] Failed to load imported types ...
Unknown type: Ppn`. Runtime results are still correct, but JIT is disabled.

## 4. Function-field call breaks under interp when a newtype is imported
With a newtype imported (forcing the interp fallback of #3), an inline function-
field call `(x.copy)(args)` / `(me.copy)(args)` resolves as `unknown symbol`.
Workaround: bind to a local first — `var f = me.copy; f(args)` — which works under
both interp and JIT. (The fn-field-as-struct-field pattern itself is fine; it is
the *call form under interp+newtype* that breaks.)

## Impact / workarounds adopted in emu/
- Domain newtypes used at all interfaces for clarity; unwrap-rewrap for math; raw
  `i64` stored in bulk arrays. Real guarantees moved to Lean4 proofs
  (`emu/proofs/*.lean`: address bijection/bounds, memcpy-length safety, queue
  invariants, region disjointness + use-after-free).
- fn-field memcpy seam binds the closure to a local before calling.

A first-class newtype would enforce #1, preserve the wrapper through arithmetic
(#2), lower under JIT (#3), and keep direct fn-field calls working (#4).

## Runtime verification (2026-07-17)

**Item #1 (no type-safety enforcement) STILL-REPRODUCES:** `mix(Lba, Ppn)` accepted and ran, printed `5` with no type error. **Item #3 (JIT cannot lower) STILL-REPRODUCES:** `HIR lowering error: Unknown type: Lba` seen during same run (JIT fallback). **Item #2 (arithmetic erases wrapper) FIXED-AT-TIP:** `(l + Lba(value:1)).value` printed `6` cleanly with no `undefined field` error — arithmetic now preserves the wrapper (matches fix credit to `612a1372a28`). **Item #4 (fn-field call under interp+import):** not independently tested (requires genuine cross-module import, out of budget).

