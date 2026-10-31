# Seed runtime `rt_bytes_to_text` uses `from_utf8_lossy`, corrupting UTF-8 scalars split across input fragments

Status: OPEN. Not a decoder defect: `os.apps.smux.client_input` is a byte-exact
passthrough. The corruption happens one layer below it, in the Rust runtime's
`[u8] -> text` conversion, which replaces malformed (truncated) UTF-8 with
U+FFFD while every pure-Simple / C runtime lane preserves the bytes verbatim.
The fix belongs in `src/compiler_rust` (seed interpreter + Rust runtime),
not in `src/lib` or `src/os`.

## Symptom

Sweep with freshly rebuilt seed `build/sweep-seed-simple-v2` (branch
`release/1.0.0`): `test/03_system/tools/smux_client_input_spec.spl` fails 3 of
15 examples (log: `build/sweep/logs/smux_client_input_spec.log`):

```
✗ should forward unknown bindings with their original prefix
  expected left to equal leftzright
✗ should preserve UTF-8 byte fragments split inside a scalar
  expected 界��� to equal 界😀
✗ should forward a prefixed unknown binding split inside its Unicode scalar
  expected ��� to equal ���
```

The two UTF-8 failures: the spec slices `text_to_bytes("界😀")` into raw
fragments (`bytes[0:1]`, `bytes[1:5]`, `bytes[5:]`), feeds each through
`std.common.text_bytes.bytes_to_text` into `client_input_feed`, and asserts
`text_to_bytes(action.data)` round-trips each fragment exactly and that the
reassembled text equals `"界😀"`. In the seed lane each truncated fragment
comes back as U+FFFD replacement bytes (`ef bf bd`), so the round trips and
the reassembly fail.

The third failure is unrelated to UTF-8: commit `59b6c5da26e`
("feat(smux): implement authoritative window zoom and interactive restore",
2026-10-25) added `if key == "z": return "toggle-zoom"` to
`_client_input_binding` (`src/os/apps/smux/client_input.spl:25`), while the
spec example at `test/03_system/tools/smux_client_input_spec.spl:83-89` still
treats `z` as an unknown binding forwarded transparently as `left\x02zright`.
Spec/impl drift from the same commit; needs a spec update or a binding
revert, separate from this bug.

## Root cause

Layer: **Rust seed runtime lane** (interpreter extern + native runtime), not
the Simple decoder, not codegen.

- The decoder (`src/os/apps/smux/client_input.spl:33-60`) operates purely on
  bytes via `text_to_bytes` / `bytes_to_text` and is byte-exact. Its own
  comment states the contract: "Raw-copy conversion preserves UTF-8 fragments
  when a read splits a scalar across text chunks" (line 38).
- `std.common.text_bytes.bytes_to_text`
  (`src/lib/common/text_bytes.spl:32-33`) is a thin passthrough to the
  runtime extern `rt_bytes_to_text`. The stdlib contract is a byte carrier:
  "Checked byte-carrier extraction is encoding-neutral ... UTF-16 and
  malformed bytes are valid external payloads here"
  (`src/lib/common/text_bytes.spl:45`).
- Seed interpreter extern:
  `src/compiler_rust/compiler/src/interpreter_extern/conversion.rs:192`
  ```rust
  let text = String::from_utf8_lossy(&bytes).into_owned();
  ```
- Rust native runtime:
  `src/compiler_rust/runtime/src/value/sffi/file_io/file_ops.rs:2280-2293`
  (packed fast path) does the same `String::from_utf8_lossy(&packed)`; its
  doc comment at 2281-2282 declares "Convert bytes to UTF-8 text, replacing
  malformed sequences with U+FFFD", and the lossy policy is pinned by the
  Rust unit test `malformed_packed_and_boxed_bytes_become_valid_replacement_text`
  (same file, ~line 3602).
- Every other lane is byte-preserving, so the lanes disagree:
  - pure-Simple core: `src/runtime/simple_core/core_array.spl:316-332`
    (`rt_bytes_to_text` copies the buffer into `rt_string_new` with no UTF-8
    validation);
  - C hosted lane: `src/runtime/runtime_core_io_exports.c:592-608`
    (`rt_string_from_byte_array`, verbatim `rt_string_new(buf, len)`);
  - C native twin: `src/runtime/runtime_native.c:10268-10284` and
    `src/runtime/runtime.c:4236-4248` (verbatim `rt_string_new(data, len)`).

`String::from_utf8_lossy` maps a truncated scalar fragment such as `[0xe7]`
(the first byte of `界`) to the 3-byte replacement character U+FFFD
(`ef bf bd`), and `text_to_bytes` then returns the replacement bytes, not the
original. Any `[u8] -> text -> [u8]` round trip over a split scalar is
destroyed in the Rust lane only.

Recent history on the suspect files: `git log -3` on
`src/compiler_rust/compiler/src/interpreter_extern/conversion.rs` shows only
extern-table registration work (`40fc660e0e6`, `4b063dd9095`,
`9ecc62bf608`) — the lossy conversion predates those; on
`src/os/apps/smux/client_input.spl` the only relevant change is the `z`
binding above.

## Repro

Probe: `build/sweep/probes/utf8_split_repro.spl` (self-attesting; direct
`bytes_to_text`/`text_to_bytes` round trips plus the full
`client_input_feed` decode path, mirroring the two failing UTF-8 examples).

```
$ timeout 240 build/sweep-seed-simple-v2 run build/sweep/probes/utf8_split_repro.spl --no-session-daemon
original bytes: e7 95 8c f0 9f 98 80
fragment bytes[0:1] roundtrip: ef bf bd (want e7)
check roundtrip bytes[0:1]: FAIL
check roundtrip bytes[1:5]: FAIL
check roundtrip bytes[5:]: FAIL
check decoder assembled == 界😀: FAIL
check prefixed split action0 == [2,240]: FAIL
check prefixed split action1 == [159,152,128]: FAIL
check prefixed split assembled == \x02😀: FAIL
RESULT: FAIL (7 checks failed)
```

(The runner prints the output twice; the seed banner and an
`[engine-demotion] ... rt_string_from_byte_array ...` splice notice precede
it.)

Not run in a passing lane here: no pure-Simple `bin/simple` release binary or
`llc` is present on this host to AOT-build the probe through the C runtime
lane (`native-build` fails with `llc not found`). The byte-preserving source
of the C/pure-Simple lanes is cited above as the parity reference.

## Decision

The smux decoder and the stdlib contract assume a byte-preserving
`[u8] <-> text` carrier (the pure-Simple canonical runtime implements
exactly that). The Rust seed lane's deliberate U+FFFD policy
(`from_utf8_lossy`, pinned by its own Rust unit test) violates that
cross-lane contract and is the defect. Repair route: make the Rust
interpreter extern (`conversion.rs:192`) and the Rust native runtime
(`file_ops.rs:2280-2293`) byte-preserving to match
`core_array.spl:316-332` / `runtime_native.c:10268`, and update the pinning
Rust unit test accordingly. Do not "fix" the smux spec or decoder to expect
U+FFFD: that would bake a lane divergence into the production contract.

Separately (not this bug): update
`test/03_system/tools/smux_client_input_spec.spl:83-89` for the `z` ->
`toggle-zoom` binding added in `59b6c5da26e`, or revert that binding line if
`z` was not intended to bind.

Prevention spec skeleton: `build/sweep/probes/utf8_split_prevention_spec.spl`
(`# authored-unexecuted: pending runner lane`) — scenarios: scalar split at
every byte boundary of 2-, 3- and 4-byte chars, consecutive multibyte chars,
mixed ASCII/multibyte, fragment boundary exactly at scalar edges, and the
prefixed-binding split path.
