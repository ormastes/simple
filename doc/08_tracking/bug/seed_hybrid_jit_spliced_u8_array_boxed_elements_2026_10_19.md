# Seed hybrid JIT: `[u8]` returned through the interpreter splice has boxed elements

- Status: open (worked around in the codec: bulk decode falls back to the per-byte copy)
- Severity: P2 — wrong bytes from `[u8]` indexing and bulk runtime calls; slow file reads under JIT
- Found: 2026-10-19, lane work/codec-native-build-and-perf, seed f49a027986fb (fileio lane)

## Symptom

Default `run` mode (JIT with `[engine-demotion] reason=hybrid-interp-splice`,
`rt_io_file_read` in the splice list). For a file starting `abcdefgh`:

```
val chunk = file_read_borrowed_bytes(fd, 8).unwrap()   # rt_io_file_read
for b in chunk: ...            # 97, 98, 99, ... (correct)
chunk[0]                       # 209 (wrong)
rt_utf8_validate(chunk)        # false (rejects non-int elements)
rt_bytes_to_text(chunk)        # nil (text length -1)
```

The same calls are correct under `SIMPLE_EXECUTION_MODE=interpreter`, and on a
packed buffer filled by `push` under JIT.

## Cause (as observed)

The spliced extern runs in the interpreter and its `Value::byte_array` is
converted back into a runtime array whose elements are boxed values, not the
packed bytes the Rust runtime's own `rt_io_file_read` (`bytes_to_runtime_array`,
`rt_byte_array_new`) returns. Iteration unboxes; `[u8]` indexing reads storage
as packed bytes; `runtime_value_array_to_bytes` (utf8_kernels.rs) rejects
non-int elements.

## Impact

Any bulk primitive or `[u8]` index on such an array is wrong under the seed
JIT. The strict codec only stayed correct because `external_copy_bytes`
normalized storage by iterating first. With the bulk fast path, JIT reads
fall back to that copy: 5 x 0.94 MB reads take 1184 ms (interpreter: 13-26 ms).

## Fix direction

Convert interpreter byte arrays back into packed runtime byte arrays at the
splice boundary (seed). Not attempted here: seed rebuild out of scope.
