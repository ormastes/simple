# Seed JIT: `[u64].push(v)` flips bit 62 when `v >= 2^63`

Found 2026-11-27 while flipping the std crypto byte API to `[u8]`
(branch `work/crypto-u8-api-20261127`). Host: aarch64 Linux (DGX GB10).
Seed: `~/.cache/cargo-target-wr-seed1126b/release/simple` (release head 11-26).

## Repro

```
fn main():
    val v: u64 = 13643789653076310793u64
    var a: [u64] = []
    a.push(v)
    var b: [u64] = [0u64; 2]
    b[0] = v
    var c: [u64] = [v, 1u64]
    var d: [i64] = []
    d.push(v as i64)
    print "push={a[0]} idx={b[0]} lit={c[0]} i64push={d[0] as u64} xor={(a[0] ^ v)}"
```

| engine | output |
|---|---|
| `SIMPLE_EXECUTION_MODE=interpret` | `push=13643789653076310793 idx=13643789653076310793 lit=13643789653076310793 i64push=13643789653076310793 xor=0` |
| `SIMPLE_EXECUTION_MODE=jit` | `push=18255475671503698697 idx=13643789653076310793 lit=13643789653076310793 i64push=13643789653076310793 xor=4611686018427387904` |

Only `.push()` into a `[u64]` is wrong; an index store, an array literal and a
push into `[i64]` are exact. The xor is exactly bit 62 (`0x4000000000000000`),
consistent with a tagged-int encode/decode of the pushed word.

## Impact

`std.common.crypto.argon2` builds its 128-word blocks with `[u64].push`, so the
JIT produced a wrong Argon2id tag (RFC 9106 §5.3 vector: got `68372ce3...`,
want `0d640df5...`). Before the `[u8]` API flip this was latent: every program
importing `blake2` demoted the whole module to the interpreter on an unrelated
ambiguous `bytes_to_hex` call, so the JIT never ran argon2.

## Workaround (in tree)

`@workaround(jit_u64_array_push_high_bit_corruption_2026-11-27)` in
`src/lib/common/crypto/argon2.spl`: every `[u64]` word buffer is pre-sized and
index-assigned. Argon2id RFC 9106 vector now passes on interpreter and JIT.

## Fix owed

Seed JIT array push lowering for `u64` element type (Rust seed,
`src/compiler_rust/compiler/src/codegen/`). Remove the workaround once fixed and
the repro above prints `xor=0` on the JIT.
