# SLH-DSA-192s/256s — Hash + n Parameterization Refactor Required

*Written: 2026-05-02. Blocker for W14-D Phase 2 (SLH-DSA-SHA2-192s + 256s).*

---

## Status

Phase 1 of W14-D-retry (SHA-512 interpreter dispatch) **landed and is
green** — see `test/unit/lib/crypto/sha512_extern_dispatch_spec.spl`
(5/5 KAT pass). Phase 2 (192s + 256s implementations + KAT specs) is
**blocked on a refactor whose scope was underestimated** by the wave
description. This bug captures the exact surface so the next attempt
can land it cleanly.

## Problem

`src/os/crypto/slh_dsa*.spl` is hardcoded to the SLH-DSA-SHA2-128s
parameter set. The "internal" entrypoints take only the variable
parameters (`d`, `h_prime`, `a`, `k`) and hardcode:

1. **n (security parameter / output truncation length)** to 16 bytes.
   - `_slh_n_128s() -> 16` is referenced unconditionally inside
     `slh_F_128s`, `slh_H_128s`, `slh_T_l_128s`, `_hash_prefix_128s`,
     `slh_keygen_internal`, `slh_sign_internal`, `slh_verify_internal`.
   - 192s requires n=24; 256s requires n=32.
2. **Hash function** to `sha256` — SLH-DSA-SHA2-192s/256s require
   **SHA-512** for F / H / T_l / PRF / PRF_msg / H_msg per FIPS 205
   §11.2.1 Table 4. There is no SHA-256 fallback for these sets.
3. **Prefix length** to `n + 48 = 64` (one SHA-256 block padding).
   192s/256s use a 128-byte SHA-512 block, so prefix = `n + (128 - n)`.
4. **m (message digest length for randomized hashing)** to 30 bytes via
   `_slh_m_128s()`. Per FIPS 205 Table 4: 192s m=39, 256s m=49.

## Files Affected

| File | LoC | Change Required |
|------|-----|-----------------|
| `src/os/crypto/slh_dsa.spl` | 392 | Generalize `_slh_n_*`, `_slh_m_*`, `_hash_prefix_*`, `slh_F_*`, `slh_H_*`, `slh_T_l_*` to take (n, hash_fn) explicitly. Add 192s/256s public wrappers. |
| `src/os/crypto/slh_dsa_wots.spl` | 433 | `wots_pk_gen_128s`, `wots_sign_128s`, `wots_pk_from_sig_128s` are hardcoded — need (n, hash_fn) variants. |
| `src/os/crypto/slh_dsa_xmss.spl` | ~150 | `xmss_node`, `xmss_sign`, `xmss_pk_from_sig` thread through n+hash. |
| `src/os/crypto/slh_dsa_fors.spl` | ~230 | `fors_pk_gen`, `fors_sign`, `fors_pk_from_sig` thread through n+hash. |
| `src/os/crypto/slh_dsa_hypertree.spl` | ~150 | `ht_sign`, `ht_verify`, `ht_pk_root` thread through n+hash. |

Total: ~1,300 LoC touched. The "thread through" pattern in pure Simple
is non-trivial because Simple does not yet have first-class function
values (no `(n, hash_fn) -> ...` callback type) — see
`feedback_text_only_byte_cliffs.md` and `language.md` ("no inheritance,
use composition"). Two viable paths:

### Option A — Sibling files per parameter set
Duplicate `slh_dsa.spl` → `slh_dsa_192s.spl` + `slh_dsa_256s.spl`
with `sha512` substituted for `sha256` and n=24/32 inlined. Same for
WOTS/XMSS/FORS/HT helpers. **Code dup ≈ 2 × 1,300 = 2,600 LoC**, but
no language-feature dependency. Downside: future bug fixes must be
applied 3× (128s + 192s + 256s).

### Option B — Tag-dispatched generic
Add an `enum HashId { Sha256, Sha512 }` and pass `hash_id: HashId`
plus `n: u64` through every internal helper. Implement an internal
`_slh_hash(id, msg) -> [u8]` that branches. **No code dup**, but
touches every existing `_128s` callsite (~80 callsites by grep).
Requires confidence that match/enum dispatch is interpreter-safe
(blocker risk per `feedback_class_trait_header_form_also_fails.md`).

## KAT Spec Cost

The 128s spec already deviates from FIPS 205 §11 Table 2 to avoid the
4-minute-per-sign cost (uses reduced d=2, h'=2, k=2, a=4 — see
`test/unit/lib/crypto/slh_dsa_128s_spec.spl` lines 19-32). 192s and 256s
under SHA-512 will be **slower** (larger blocks, larger n, deeper trees
at full Table 2 params), so the same reduced-parameter strategy must be
applied. The full-parameter KAT remains gated behind `SLH_DSA_FULL_KAT`
env var.

## What's Already Unblocked

The SHA-512 runtime dispatch (Phase 1) **does** unblock:

- HKDF-SHA-512 / HMAC-SHA-512 interpreter-mode KAT specs (no SLH-DSA
  refactor needed).
- Ed25519 interpreter-mode coverage (`src/os/crypto/ed25519.spl:17`
  comment about SHA-512 dispatch gap is now stale).
- Any future caller of `os.crypto.sha512.sha512()` under
  `bin/simple test`.

## References

- `doc/02_requirements/feature/sha512_interpreter_dispatch.md` — Phase 1
  FR (now satisfied).
- FIPS 205 §11 Table 2 — parameter sets.
- FIPS 205 §11.2.1 Table 4 — SHA-2 family hash specifications.
- `.claude/memory/feedback_no_coverups.md` — root-cause-fix discipline
  that forces Option A or B over half-a-spec.
- `.claude/memory/feedback_compile_mode_false_greens.md` — interpreter-
  mode verification discipline (Phase 1 spec exercises this).
- `test/unit/lib/crypto/slh_dsa_128s_spec.spl` — reduced-parameter
  pattern to mirror for 192s/256s.
