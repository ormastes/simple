# Chromium oracle Simple caller byte-pointer projection fails in seed interpreter

## Status

Fix implemented; integration rerun deferred by the session's three-cycle cap.
It still blocks the hosted Simple-to-native Chromium oracle ABI integration gate
until the next admitted run passes.
The native C fixture's own `dlopen` test passes, but the Simple caller does not
yet transmit the complete JSON request through the integer-only dynamic-call
bridge. This is fixture evidence only and must not be reported as Chrome/GPU
evidence.

## Reproduction

```text
sh test/fixtures/chromium_primitive_oracle/run_simple_caller_fixture.shs
```

The C fixture first reports:

```text
CHROMIUM_ORACLE_FIXTURE_DYNLOAD_PASS provenance=fixture-not-chromium gpu=unavailable
```

The Simple caller then loads and creates a session successfully but reports:

```text
chromium-oracle-native-integration: run failed: unsupported-primitive:unsupported-primitive
```

The request literal contains all seven fixture keys (`rect`, `text`, `image`,
`pointer`, `keyboard`, `scroll`, `resize`). Therefore at least one byte range
observed by the C provider differs from the Simple `[u8]` value projected with
`rt_array_data_ptr_text` through `spl_wffi_call_i64` in the Rust bootstrap
interpreter lane.

## Required correction

Provide a checked, ownership-explicit dynamic-call byte-span operation rather
than requiring callers to reinterpret a managed `[u8]` value as an integer raw
pointer. It must carry `(base, length)`, pin storage for the entire call, reject
non-byte arrays, and preserve caller ownership for output buffers and length
slots. The same integration gate must pass under an admitted self-hosted binary.

## Implemented correction

The caller now uses the existing canonical
`spl_wffi_call_i64_with_bytes` operation for its immutable request. The runtime
pins and bounds that owned span for exactly one foreign call. Response storage
and its eight-byte length slot now come from `rt_byte_array_new_len`, whose
packed basis has stable data pointers; ordinary boxed arrays are no longer
reinterpreted as native buffers. The dynamic module explicitly exports both the
checked and unchecked byte-span operations. Both modified Simple modules pass
the focused source check, but the integration command was not repeated after
the prior three failed cycles.

## Acceptance

1. The reproduction emits `chromium-oracle-native-integration: PASS fixture-only`.
2. The response has `oracle_identity=fixture-not-chromium` and
   `device_origin_readback=false`.
3. Exact-once release passes and duplicate release is rejected.
4. A native-compiled caller passes once the compiler supports the required
   checked dynamic-loader constructs.
