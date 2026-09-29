# `black_box_spec.spl` cannot detect `rt_black_box` breaking — `?? v` substitutes the original on nil

- **Filed:** 2026-08-31
- **Severity:** MEDIUM — test-integrity defect on a security-relevant symbol (not a runtime defect)
- **Status:** RESOLVED 2026-08-31 — `test/01_unit/lib/crypto/rt_black_box_direct_spec.spl` landed beside the old spec; discrimination proven by an executed negative control (see "Negative-control evidence"). The `?? default`-between-spec-and-extern lint idea remains an open follow-up.
- **Found by:** `doc/08_tracking/test/rt_test_coverage_audit_2026-08-31.md` §5 / §7 R3

## Symptom

`test/01_unit/lib/crypto/black_box_spec.spl` exists and passes 5/5, but every
one of its assertions routes through the stdlib wrapper:

```
pub fn black_box(value: i64) -> i64:
    rt_black_box(value) ?? value          # std.crypto.constant_time, constant_time.spl:22
```

If `rt_black_box` returns nil — unregistered extern, broken registration,
stubbed lane — `?? value` substitutes the original argument and **all five
assertions still pass**. What the spec pins is the wrapper's fallback, not
the runtime entry point.

## Measured, not hypothesised

The audit's replacement spec executes this as `B6 NEGATIVE CONTROL`: a
deliberately nil-returning stub passes the wrapper-shaped assertions and
fails the direct-call assertion, in the same run. That is the definition of a
non-discriminating test: its verdict does not depend on the property it
claims to test.

## Why it matters

`rt_black_box` is the optimization barrier that keeps `ct_eq`, ML-KEM
rejection sampling, and Curve25519 conditional swap from being rewritten into
data-dependent early-exit branches. A silently-nil `rt_black_box` removes
the barrier while the whole crypto spec suite stays green.

## Generalisation (the actionable part)

Any `?? default`, `.unwrap_or`, or `or_else` **between a spec and an extern**
converts a hard failure into a silent substitution; the audit's §0b ceiling
model credits such a symbol as "reached" while it is effectively untested.
This shape is mechanically detectable. Follow-up already recommended by the
audit (§8 item 3): a lint/guard for the `?? default`-between-spec-and-extern
pattern.

## Resolution path

- Keep the old spec (the wrapper's fallback IS worth pinning — that behavior
  is deliberate).
- Land the audit §6.2 direct-call spec beside it (`extern fn rt_black_box`
  called without the wrapper, plus the negative control).
- File the lint idea as its own todo if not picked up with this record.

No runtime code changes. Nothing platform-specific; the specs are pure Simple
and behave identically on Linux/macOS/Windows.

## Correction measured at filing time (2026-08-31)

The draft attributed the silent-nil to "the exact failure mode of the
unregistered-extern class". **Measured otherwise on the deployed Windows seed
interpreter:** an extern whose name is not registered fails LOUDLY —
`semantic: unknown extern function: <name>` — and even the wrapper-shaped old
spec fails on it (measured 1/5 passing). The class this record is about is
narrower: a REGISTERED implementation that returns nil (a stubbed lane, a
broken registration body, or a native-lane null slot of the
`rt_unwrap_or_trap` kind). That is what `?? value` hides and what only the
direct spec catches. The unregistered-extern record
(`unregistered_extern_silent_nil_2026-08-01.md`) still applies to lanes
without the loud check.

## Negative-control evidence (executed 2026-08-31, Windows seed)

The REAL registered extern was broken and restored, and both specs run
unmodified each time via `SIMPLE_BINARY` pointed at the rebuilt seed:

1. **Break:** `interpreter_extern/file_io.rs` `rt_black_box` body replaced
   with `Ok(Value::Nil)`; seed rebuilt (`cargo build --release --bin simple`).
2. **Measured with the nil stub:**
   - OLD `black_box_spec.spl`: **5/5 PASS** — blind, exactly as this record
     claims (`?? value` substitutes the argument).
   - NEW `rt_black_box_direct_spec.spl`: **1/7 — B0..B5 all FAIL** (only the
     in-spec local-stub scenario B6 passes, by design).
3. **Restore:** stub reverted (`git checkout` of file_io.rs, diff empty),
   seed rebuilt; both specs re-run: OLD 5/5 PASS, NEW 7/7 PASS.

Secondary measurement: with an UNKNOWN extern name instead (a nonexistent
`rt_black_box_*` symbol), the interpreter fails loudly
(`semantic: unknown extern function`) and even the old spec fails 4/5 — see
the correction section above for why that class is not the hidden one.
