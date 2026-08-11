# `window_record_encode` is imported by the SPM client but defined nowhere; its spec only length-compares two self-generated encodings

**Status:** OPEN — architectural/out-of-scope for a measurement lane (needs SPM
wire-format investigation before an encoder can be written; re-confirmed
2026-08-10)
**Found:** 2026-08-04

## Symptom

```
SIMPLE_TIMEOUT_SECONDS=0 bin/simple test --no-cache --timeout 800 test/01_unit/os/compositor
#   FAIL test/01_unit/os/compositor/wm_spm_client_spec.spl (0 passed, 2 failed, 310ms)
#   Error: semantic: function `window_record_encode` not found  (x2)
```

The 310 ms runtime is the tell: this is a resolution failure at load, not a
behavioural one.

## Root cause (proven)

`src/app/simple_process_manager/wm_spm_client.spl:21` imports it:

```simple
use lib.common.win_fs.window_record.{WindowRecord, window_record_encode}
```

and calls it at `:160`, inside a helper whose docstring asserts a contract that
nothing implements:

```simple
fn _encode_record_meta(rec: WindowRecord) -> [u8]:
    """Use the canonical WindowRecord encoding expected by SpmService."""
    window_record_encode(rec)
```

But `src/lib/common/win_fs/window_record.spl` is **57 lines total** and its
entire API is:

```
:14  struct Rect:
:20  struct BufferRef:
:25  class WindowRecord:
:47  fn window_mark_destroyed(rec: WindowRecord) -> WindowRecord:
```

There is no `window_record_encode` — and no `WindowState` either, though
`wm_spm_client_spec.spl:15` imports that from the same module. An unresolved
`use` is only a WARNING, so both the module and the spec load and the failure
surfaces at the first call.

**Re-verified 2026-08-10:** `window_record.spl` has since grown a
`WindowState` enum (unrelated partial progress since this doc was filed), but
`window_record_encode` is still declared nowhere in `src/` — confirmed with
`grep -rn "fn window_record_encode" src/lib src/app src/os` (zero hits). The
core defect and the reasoning for leaving it open (writing an encoder from
this spec alone would prove nothing about the actual wire format) are
unchanged.

## Why not fixed now — and a vacuity warning

The obvious "fix" is to write an encoder. **Do not do that from the spec.** The
spec cannot tell you the wire format; its only two assertions are

```simple
:34   expect host_bytes.len() to_equal os_bytes.len()
:46   expect direct.len() to_equal via_client.len()
```

Both compare the length of one encoding against the length of *another encoding
produced by the same missing function*. Any self-consistent encoder — including
a wrong one, including one that returns a fixed-length constant — satisfies
them. Greening this spec would therefore prove nothing about the "canonical
WindowRecord encoding expected by SpmService" that `_encode_record_meta`
claims to produce, and would convert a loud failure into a silent false green
on a serialization contract that crosses a process boundary.

Closing this properly needs the SpmService side of the wire format identified
(what actually decodes these bytes), the encoder written against *that*, and
the spec's length-only assertions replaced with byte-level assertions against a
recorded reference encoding. That is an SPM/transport lane, not a compositor
measurement lane.
