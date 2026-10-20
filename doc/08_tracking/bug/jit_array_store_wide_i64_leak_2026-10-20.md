# JIT: storing a full-width i64 into an array allocates and is never freed

- Date: 2026-10-20
- Status: open
- Found by: pure-Simple SHA-512 work (`src/lib/common/crypto/sha512.spl`)
- Binary: `bin/release/aarch64-unknown-linux-gnu/simple` (Rust seed), default JIT mode

## Symptom

Under the JIT, each store of an i64 whose value is outside the tagged-int
range into an `[i64]` array grows RSS by about 48 bytes, and the memory is not
reclaimed. Locals holding the same values do not grow. The interpreter does
not show it.

Reproducer (4,000,000 stores into an 80-element array):

```
fn main():
    var w: [i64] = [0; 80]
    var x: i64 = BASE
    var n = 0
    while n < 4000000:
        x = x + 1
        w[n & 63] = x
        n = n + 1
    print "{w[3]}"
main()
```

| BASE | wall | max RSS |
|------|------|---------|
| 5 | 0.17 s | 33 MB |
| 8070450532247928832 | 1.09 s | 221 MB |

The same loop with the value kept in a local and no array store stays at
33 MB for both values.

## Impact

A first SHA-512 rewrite with the message schedule in an 80-word array reached
428 MB RSS for PBKDF2-HMAC-SHA-512 at c=80000 under the JIT (compression
alone: 40 MB at 2,000 calls, 127 MB at 40,000). The shipped version keeps the schedule and
working variables in locals, so its RSS stays flat (125 MB at c=80000, the
same as at c=4096). Any other 64-bit hash, cipher or bigint code that keeps
full-width words in arrays still pays this cost.

## Related

- `[u64]` element reads shift arithmetically in the interpreter
  (`(u[0] >> 60) as i64` gives -1 for `u[0] = 2^64-1`, JIT gives 15). This is
  why the SHA-512 code stores no state in `[u64]` arrays.
