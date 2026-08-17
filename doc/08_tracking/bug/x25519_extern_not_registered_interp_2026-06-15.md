# X25519 unregistered bare extern removed

**ID:** x25519_extern_not_registered_interp_2026-06-15
**Date:** 2026-06-15
**Severity:** P1 (raised 2026-08-17 from P3) — X25519 returned the WRONG shared
secret for every input. The original P3 framing described a dead optimization
path; the pure-Simple ladder it fell back to had never computed a correct
result.
**Status:** Extern removal 2026-07-15 was correct but was NOT a fix — the
remaining implementation was broken. Actually fixed and verified 2026-08-17.

## The 2026-07-15 closure was unproven, and wrong (2026-08-17)

This doc closed with "Verification remaining" and no runtime PASS claimed. That
caution was justified: when the verification was finally performed,
`test/01_unit/lib/common/crypto/typed/asym_spec.spl` was
`13 total, 11 passed, 2 failed`. The two failures were the RFC 7748 5.2 and 6.1
hex assertions — the only two examples in the file that check an X25519 *value*
rather than a length.

Removing the unregistered `rt_tls13_x25519` extern was the right call, but it
left the pure-Simple Montgomery ladder as the sole path, and that ladder was
never correct. Measured before the fix:

```
SHARED_GOT  23af31d7670b07dcab03ca5d0dc6c7b8c3d2f2700fab5546f481ab757e6c3600
SHARED_WANT c3da55379de9c6908e94ea4df28d084f32eccf03491c71f754b4075577a28552
PUB_GOT     7a329a15b1231788b8f421bd82921568fde4b035d864588df33833b2f8672a00
PUB_WANT    8520f0098930a754748b7ddcb43ef75a0dbf3a0d26381af4eba4a98eaa9b4e6a
DH_AGREE    no
```

Note both wrong outputs end in `00`, and that `x25519(a, pub_b)` did not even
equal `x25519(b, pub_a)` — the primitive was not usable for key agreement.

### Four independent root causes

1. **`_fe_mul` omitted the mixed-radix doubling.** The 10-limb representation is
   radix 2^25.5 — even limbs hold 26 bits, odd limbs 25 — so a product
   `a[i]*b[j]` with `i` and `j` both odd lands one bit low and needs a factor
   of 2. The unrolled schoolbook had no such factors, so it did not compute
   `a*b` at all.
2. **`_fe_from_bytes` used a layout that was not self-consistent**, and read
   `_load3(b, 31)`, touching `b[32]`/`b[33]` — past the end of a 32-byte key.
3. **`_fe_to_bytes` was wrong twice.** Its canonical-reduction probe read
   `(19*h9 + 2^25 + h0*h0) / 2^26`; the `h0*h0` term belongs to no reduction,
   and the constants were off by a factor of two, so values came back as `p+1`
   rather than `1`. Separately it assumed limb `h5` began at bit 127 instead of
   128, giving `h5` three byte slots instead of four — every byte from index 15
   on shifted down by one, with a literal `0x00` appended to pad the length back
   to 32. That padding is the trailing `00` above.
4. **The ladder began from a zeroed `x_3`.** `var x_3 = u` hit a language
   defect: binding one `[u64]` variable to another yields an array of the
   correct length whose elements are all zero. `x_3` was therefore the point at
   infinity and the ladder collapsed. Filed separately as
   `doc/08_tracking/bug/typed_array_variable_binding_zeroes_elements_2026-08-17.md`
   and worked around in-place with a comment pointing at that record.

Causes 1-3 are genuine defects in this repository's crypto source. Cause 4 is a
compiler/interpreter defect that this code merely tripped over.

### Verification actually performed

Field layer, by direct probe: byte round-trip exact; `3*5 == 15`;
`(2^80)^2 == 2^160`; `2^100 * 2^50 == 2^150`; bit-doubling correct at every
position 20..254; multiplication associative and distributive on full-size
elements; `a * a^-1 == 1`.

End to end:

```
SHARED_GOT  c3da55379de9c6908e94ea4df28d084f32eccf03491c71f754b4075577a28552  = RFC 7748 5.2
PUB_GOT     8520f0098930a754748b7ddcb43ef75a0dbf3a0d26381af4eba4a98eaa9b4e6a  = RFC 7748 6.1
DH_AGREE    yes
```

`test/01_unit/lib/common/crypto/typed/asym_spec.spl` now reports
`Results: 13 total, 13 passed, 0 failed` (`SPEC FILE VERDICT: ... declared>=13
executed=13 passed=13 failed=0 dropped=0`). No assertion was weakened; the two
previously-failing expectations are unchanged RFC constants.

Fix commits: `7a08ef912e0` (field arithmetic), `cb2d0f31577` (ladder).

Reproducing and prevention specs:
- `test/01_unit/lib/common/crypto/x25519_rfc7748_kat_spec.spl` — RFC 7748 5.2
  and 6.1 vectors plus both-sides DH agreement.
- `test/01_unit/compiler/typed_array_variable_binding_spec.spl` — pins the
  typed-array copy semantics behind cause 4, so the same class of silent
  wrong-answer cannot recur unnoticed.

## Summary

`src/lib/nogc_async_mut_noalloc/tls/x25519.spl` declared:

```
extern fn rt_tls13_x25519(scalar: [u8], u_coord: [u8]) -> [u8]
```

This extern was not implemented or registered in the interpreter's SFFI
dispatch table (`src/compiler_rust/compiler/src/interpreter_extern/`). Related
runtime manifest symbols use different names:
- `rt_tls13_x25519_public_key`
- `rt_tls13_x25519_shared_secret`

(listed in `runtime_symbols.rs` and used separately by `ssh_session_kex.spl`).

## Historical behaviour

The unimplemented extern was called before the pure-Simple Montgomery ladder.
Interpreter modes did not share a reliable unknown-extern fallback contract,
so standalone run mode could fail before reaching the ladder.

The existing typed-wrapper spec contains RFC 7748 §5.2 and §6.1 assertions,
but those assertions have not been rerun for the current source change.

## Resolution

- Removed the `rt_tls13_x25519` declaration and its unconditional fast-path
  call.
- Reused the existing pure-Simple Montgomery ladder as the sole implementation.
- Kept the existing RFC 7748 KAT assertions; no new test framework or fixture
  was added.

## Verification remaining

- Run `test/01_unit/lib/common/crypto/typed/asym_spec.spl` and record the RFC
  KAT result.
- Run a standalone interpreter path through the existing typed wrapper and
  confirm that no unknown-extern diagnostic occurs.
- No runtime PASS is claimed by this source-only update.
