# Seed datetime i32 timestamp ABI

## Status

Open. The hosted runtime timestamp ABI uses `i64` microseconds, but the legacy
seed-library declarations in `tooling/time_utils.spl` and
`host/async_nogc_mut/datetime.spl` declare timestamp inputs and results as
`i32`. Current Unix microsecond timestamps cannot fit that representation.

## Required atomic fix

- Keep calendar components as `i32`.
- Change timestamp-bearing extern inputs/results and `DateTime.timestamp` /
  `DateTime.from_timestamp` to `i64`.
- Widen duration microsecond arithmetic that participates in timestamp math.
- Add current-epoch, pre-epoch, and round-trip coverage before changing the
  seed library ABI.

This is separate from the hosted C/common arithmetic correction; silently
casting only one declaration would preserve truncation at another boundary.
