# BUG: `push(x as u8)` grows a `[u8]` whose storage is not byte-packed

**Status:** OPEN
**Found:** 2026-09-06 (macOS aarch64, `src/compiler_rust/target/debug/simple`, interpreter path)
**Severity:** high — silently corrupts every binary decode built by hex/byte
reassembly. It made 100% of process-transfer frames decode as
`invalid-envelope`, i.e. the parent-authoritative process transport accepted
zero results, with no diagnostic and exit 0.

## Symptom

Two `[u8]` values with byte-identical, individually-readable elements are read
differently by the same reader function.

`repro_u8.spl` (the `std.common.crypto.hmac` import is only there to force the
module onto the interpreter path — see "Trigger" below):

```
use std.common.crypto.hmac.{hmac_sha256}
use std.common.structural.wire.{wire_put_u64, wire_get_u64}

fn main():
    var a: [u8] = []
    a = wire_put_u64(a, 1788684218584431)      # pushes `(v >> n) & 0xFF`  (i64)
    var b: [u8] = []
    var i = 0
    while i < a.len():
        b.push((a[i] as i64) as u8)            # pushes an `as u8` value
        i = i + 1
    print "a_get={wire_get_u64(a, 0)}"
    print "b_get={wire_get_u64(b, 0)}"
```

Observed:

```
a_len=8 b_len=8
  a[0]=111 b[0]=111
  a[1]=205 b[1]=205
  a[2]=118 b[2]=118
  a[3]=127 b[3]=127
  a[4]=204 b[4]=204
  a[5]=90  b[5]=90
  a[6]=6   b[6]=6
  a[7]=0   b[7]=0
a_get=1788684218584431      <- correct
b_get=111                   <- WRONG (0x6f, i.e. byte 0 followed by seven zeros)
```

Element-by-element the two arrays are equal, and `b[k]`, `b[off + k]` and
`b[k] & 0xFF` all read correctly from Simple. Only a consumer that reads the
backing storage as packed bytes disagrees: `wire_get_u64(b, 0)` returns
`b[0]` and then seven zeros, which is exactly what one byte per machine word
looks like when read as eight consecutive bytes.

Copying the elements out into a fresh array with `c.push(a[j])` restores
correct behaviour (`c_get` is right). Giving the pushed value an explicitly
typed `u8` local (`val byte_val: u8 = ... as u8; d.push(byte_val)`) does NOT
help (`d_get=111`), so this is the cast's value representation, not inference.

## Trigger

Only on the interpreter path. Adding any import that drags in
`std.common.crypto.types` makes the whole module fail HIR lowering
(`stdlib import std.common.crypto.types resolves from the project stdlib roots
only`) and drop to the interpreter, where the defect appears; the same source
under JIT is correct. Any spec that hashes (`sha256_text`) therefore runs the
broken path.

## Impact found in the field

`src/lib/common/structural/transfer/process_frame_codec.spl:131` rebuilt the
wire from the armored hex line with `wire.push((hi * 16 + lo) as u8)`. Every
frame produced a byte-identical-looking array that
`decode_process_transfer_frame` rejected as `invalid-envelope`, so
`ParentCommitPipedResultReaderV1` counted `accepted=0, rejected=1` for a frame
it had just decoded correctly. Worked around in place by masking instead of
casting (`push((hi * 16 + lo) & 0xFF)`), which is the idiom `wire_put_u64`
already uses.

**Same pattern, not yet audited:**
`src/lib/common/structural/parse/parse_types.spl:122` — `out = out.push(raw[i] as u8)`.

## Expected

`[u8]` storage must be byte-packed regardless of whether the pushed expression
is an `as u8` cast or a masked `i64`, or the two forms must not both typecheck
against `[u8]`.

## Specs

- Reproducing + generalization:
  `test/01_unit/lib/common/structural/u8_push_byte_packing_spec.spl`
  (`@tag:in-development` -- honestly RED until this defect closes; the first
  `it` replays the exact 64-bit case, the second generalizes to the 32-bit
  reader and to the `parse_types.spl:122` construction shape).
- Field coverage of the worked-around call site:
  `test/03_system/feature/language/parent_commit_piped_result_spec.spl`
  ("should validate, commit, and close one fragmented child result" went from
  7 failed checks to 5 with the mask workaround in place).
