# Seed interpreter: `[u8]` parameter stays boxed, so every mux key-encode admission is refused

Status: OPEN. Not a stdlib defect: the smux codec's size computation is exact.
This is the known OPEN gap #4 of
[seed_u64_signed_compare_and_u8_data_ptr_2026-10-19.md](seed_u64_signed_compare_and_u8_data_ptr_2026-10-19.md)
(`[u8]` params/returns not yet coerced to packed `ByteArray` in the seed
interpreter). The fix belongs in `src/compiler_rust` (seed interpreter
parameter coercion), not in `src/lib` or `src/os`.

## Symptom

Sweep with freshly rebuilt seed `build/sweep-seed-simple-v2` (branch
`release/1.0.0`): `test/01_unit/os/apps/smux/core_mux_key_codec_spec.spl`
fails 16 of 19 examples; all 16 failures are the identical error and only the
3 rejection examples pass:

```
semantic: called unwrap on Err: MuxErrorV1(observed_revision: nil, cleanup_pending: false, commit_state: MuxCommitStateV1::NotApplied, request_id: 0, detail: key byte allocation mismatch, kind: MuxErrorKindV1::Unavailable, affected: [])
```

Log: `build/sweep/logs/core_mux_key_codec_spec.log`
(`Results: 19 total, 3 passed, 16 failed`). Sibling sweep specs failing the
same way: `input_queue_spec.spl`, `resize_revision_admission_spec.spl` (1
example each), `smux_app_spec.spl`.

## Root cause

The error literal is emitted only at
`src/os/apps/smux/core_mux_key_codec.spl:21-22`
(`core_mux_key_bytes_checked_v1`), which delegates to
`std.common.text_bytes.text_byte_extraction_checked`
(`src/lib/common/text_bytes.spl:48-58`). That guard refuses when:

```
src/lib/common/text_bytes.spl:56
    if rt_array_data_ptr(bytes) == 0 or bytes.len() != expected_length:
        return Err(TextByteBufferError.AllocationFailed)
```

Hand computation for the minimal case `Scalar(97, false, false, false)`
(plain `a`, budget 65536): the first encoding pass demands
`core_mux_key_bytes_checked_v1(1, [97u8])` — demanded length 1, actual
carrier length 1 (`bytes.len()` verified 1 in the failing lane, element read
works). There is no size mismatch anywhere in the codec: named keys 1/3/4
bytes, F-keys 3/5/6/7 bytes, scalar 1-4 bytes + optional Alt prefix, and the
two-pass whole-request sizing at `core_mux_key_codec.spl:117-135` is exact.
The same probe passes under `build/sweep-seed-simple-v2 run` (2/2 Ok) and
fails under `build/sweep-seed-simple-v2 test` (2/2 Err).

The failing condition is the first disjunct: `rt_array_data_ptr(bytes) == 0`.
Per `src/compiler_rust/compiler/src/interpreter_extern/memory.rs:2020-2035`,
0 is the documented INVALID answer for a boxed `Value::Array` ("a bare literal
argument"). In the seed interpreter test lane, a `[u8]`-typed *parameter* is
not run through `coerce_to_declared_type`
(`src/compiler_rust/compiler/src/interpreter/node_exec.rs:47`; scalar params
coerce, `[u8]` params/returns do not — documented OPEN gap #4 in the
2026-10-19 bug doc, review 2026-10-20). So a literal `[97u8]` arrives at the
extern still boxed, the guard reports `AllocationFailed`, and the smux seam
maps it to "key byte allocation mismatch". Every successful encode path dies
at the same seam; rejection examples pass because they expect `Err`.

## Repro

Probe: `build/sweep/probes/mux_key_alloc_repro.spl` (direct seam call plus the
production encode path for one plain `a`).

```
$ timeout 240 build/sweep-seed-simple-v2 test build/sweep/probes/mux_key_alloc_repro.spl --no-session-daemon
Mux key allocation repro
  ✗ direct admission seam admits a one-byte carrier
    expected false to equal true
  ✗ encodes plain 'a'
    semantic: called unwrap on Err: MuxErrorV1(observed_revision: nil, cleanup_pending: false, commit_state: MuxCommitStateV1::NotApplied, request_id: 0, detail: key byte allocation mismatch, kind: MuxErrorKindV1::Unavailable, affected: [])
literal len = 1
first element = 97
  ✓ literal array length is sane in this lane
3 examples, 2 failures
```

Same probe under `run` (not `test`) on the identical seed build:

```
$ timeout 240 build/sweep-seed-simple-v2 run build/sweep/probes/mux_key_alloc_repro.spl --no-session-daemon
direct checked Ok: [97]
encode 'a' Ok: [97]
```

## Decision

Spec expectation skew is ruled out: the spec asserts only the documented
production contract of `core_mux_keys_bytes_v1` /
`core_mux_key_bytes_checked_v1` (exact byte oracles, exact budgets), and the
identical code satisfies every example in the `run` lane. This is the
already-tracked seed interpreter gap (`[u8]` parameter coercion). Repair
route: extend `coerce_to_declared_type` application to `[u8]` parameters and
returns in the seed interpreter (gap #4), after which the sweep spec should
pass without touching `src/os/apps/smux/core_mux_key_codec.spl` or
`src/lib/common/text_bytes.spl`. Do not "fix" the smux seam by adding a
per-byte fallback there: `text_byte_extraction_checked` intentionally reports
boxed carriers as `AllocationFailed`, and `utf8_bytes_valid` callers already
handle that documented signal.

Prevention spec skeleton: `build/sweep/probes/mux_key_alloc_prevention_spec.spl`
(`# authored-unexecuted: pending runner lane`) — scenarios: minimal fixed
key, modifier combinations, F-keys 1-24, Unicode boundaries, exact-max
payload, over-budget rejection.
