# Seed: exported const initialized by a unit constructor fails at import

- Seed: `C:/dev/keep/seeds/simple-local-20261125.exe`, Windows host, 2026-11-26.
- Found by: pure-Simple container lane P0 (`SOSIX_CONTAIN_CPU_RATE_MAX_V1`); the lane worked around it with a private `i64` const, so the max is not part of the public contract.

## Repro
`m/rate.spl`:
```
pub unit RateV1: i64
pub const RATE_MAX = RateV1(10000)
export RateV1, RATE_MAX
```
`use.spl`:
```
use m.rate.{RateV1, RATE_MAX}

fn main():
    print(RATE_MAX.value)
```
`simple run use.spl` →
```
HIR lowering error: Unsupported feature: cannot infer field type while lowering main: struct 'ANY' field 'value'
error: semantic: use.spl:1:1: function `RateV1` not found
```
The same const used inside its own module prints `10000` (interpreter fallback; the JIT still fails to infer the field type).

## Expected
An exported const whose initializer is a unit constructor imports and evaluates like a literal const, and the JIT types it as the unit.
