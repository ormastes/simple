# std ed25519 leaves secret temporaries unwiped (2026-11-19)

Status: PARTIALLY FIXED 2026-11-20 by milestone_0055 and milestone_0058 (NOT_RUN, no runnable binary); the entropy hex text and the Windows store text copies are fixed by milestone_0058; remaining residue is listed under "Still unwiped" (milestone_0055) minus those two items, plus the milestone_0058 "Remaining" list. Was: OPEN. Residual of `doc/08_tracking/bug/host_identity_private_parser_seed_copies_unwiped_2026-11-18.md`.

`src/lib/common/crypto/ed25519.spl`: `ed25519_pubkey` and `pure_ed25519_sign` keep the SHA-512 digest of the seed
(`h`), the clamped scalar (`a`), the nonce prefix, `r`, and field/scalar limb temporaries (`ed_scalar_mul_basepoint`,
`ed25519_field.spl`, `ed25519_scalar.spl`) as plain `[u8]`/integer values that are never passed to
`secure_zero_u8_slots`. The caller (`host_identity_key_v1.spl`) wipes every buffer it owns (seed, check, entropy
bytes, body, raw) but cannot reach these.

Not fixed in the host-identity lane: the temporaries are spread across SHA-512, scalar reduction and point
multiplication (limb arrays and i64 intermediates with no wipe primitive for integer locals), so a contained change
is not possible. Fix needs a std-level pass: wipe `h`/`a`/prefix `[u8]` buffers at the end of each entry point and
decide the policy for limb temporaries. Needs a spec that cannot observe locals today, so it also needs a test hook.

## Update 2026-11-19 (milestone_0043, Opus re-review B P2-2/P2-3/P3-6/P3-7; source-authored, NOT_RUN)
The std internals above are not the only unwiped copies, and earlier text understated that. Status per copy in
`src/app/orchestrator/host_identity_key_v1.spl`:
- Fixed: the base64 decoder kept its four pending sextets in a fresh `[i64]` each quad (about 86 dropped arrays per
  key file). It now uses one 4-byte `[u8]`, resets it in place, and wipes it (checking the wipe) on every exit. A failed
  decoder wipe returns `host-identity-key-buffer-wipe` instead of a silent `[]`.
- Fixed: encode built the base64 body as text and the PEM as a growing text, about six prefixes of the private body.
  `host_identity_pem_encode_v1` now writes the armour straight into one pre-sized `[u8]`. The output is byte-identical
  (spec ENCWIPE-08).
- Fixed (P3-7): the armour layout is canonical. Every line is 70 characters except a non-empty last line, LF-terminated.
- OPEN: `host_identity_key_generate_v1` receives the 36 entropy bytes as immutable hex TEXT from `sosix_random_hex`.
  That is a plaintext copy of the seed and check, and it cannot be wiped. The only entropy API returns text. Removing
  this copy needs a bytes-returning entropy extern, which is a runtime change and is not made here.
- OPEN: the returned private file `[u8]` is the caller's key-file buffer. Whether it is wiped after it is written is the
  caller's decision (`host_identity_command_v1.spl`).
- OPEN (not in this change): store-read error paths in `host_identity_command_v1.spl` drop `bytes` unwiped (REVIEW_B
  P3-11).

## Update 2026-11-20 (milestone_0055 STORE/CRYPTO WIPE; source-authored, NOT_RUN)
Status: PARTIALLY FIXED. The named `[u8]`/`[i64]` secret buffers that the store and the std derive/sign entry points
own are wiped at their owning storage (moved into a sole-holder `var`, source field emptied, then `secure_zero_*`), and
the secret byte buffers on this path are pre-sized so no growth reallocation frees a partial copy. What is left is
listed under "Still unwiped" with the exact reason. Specs (NOT_RUN): test/01_unit/lib/crypto/ed25519_secret_temporaries_wipe_spec.spl
(EDWIPE-01..05) and test/01_unit/lib/nogc_sync_mut/io/host_identity_store_secret_wipe_v1_spec.spl (STWIPE-01..03).
Byte identity of the refactor is also pinned by test/01_unit/lib/crypto/ed25519_rfc8032_spec.spl.

Fixed in `src/lib/common/crypto/ed25519.spl` (no public signature changed; the borrowed seed is never wiped):
- H(seed) and H(prefix || M) go through a private `_pure_ed25519_sha512_secret`. It drives the sha512 family primitives
  itself (as pbkdf2 does), so the widened `[i64]` input copy, the state words, the block words (which still hold the
  last input block) and the digest words are wiped. Public preimages (H(R || A || M), verify) keep the old bridge and
  pay nothing.
- `h`, the clamped scalar `a`, the reduced scalar (`_pure_ed25519_reduce_32_to_scalar`, whose 64-byte widened copy is
  now pre-sized and wiped), the nonce preimage (written straight into one pre-sized buffer; the separate `prefix` copy
  is gone), the nonce hash and `r` are wiped before `ed25519_pubkey` / `pure_ed25519_sign` return.
  `pure_ed25519_keypair_from_seed` now delegates to `ed25519_pubkey` (same output).
- `_pure_ed25519_clamp` and `ed25519_scalar.spl` `_limbs32_to_bytes` (every `sc_reduce` / `sc_muladd` output, i.e. the
  reduced scalar, `r` and `S`) built their result by `push`; both are now pre-sized (byte-identical output).
- Wipes are best effort: these std functions return no error, so an unverified wipe cannot refuse. The private
  `_ed25519_pubkey_run` / `_pure_ed25519_sign_run` report the verified-wipe count (7 / 13) for specs.

Fixed in the store the orchestrator reads keys through (`src/lib/nogc_sync_mut/io/host_identity_store_linux_v1.spl`):
- The `malloc` buffer `pread` fills and the one `write` drains in publish held the whole PEM and were freed as is. Both
  are zeroed (`volatile_write_u8`) before `free`, on the error and success exits (`identity_linux_free_wiped_v1`).
- The `[u8]` copy of the file grew by `push`, handing partial key prefixes back to the allocator on each reallocation.
  It is now pre-sized.
- Refusals after the copy exists (read-changed x2, file-encoding, close-unconfirmed) dropped it unwiped. Each wipes it
  first. The NUL scan only sets a flag, so no wipe runs while the loop iterator still holds the buffer.
- `path_v1` (called by `host_identity_command_v1` with the `.key` leaf) re-read the whole private key just to prove the
  target and dropped the bytes. It now takes them out of the read result and wipes that sole holder (Linux and Windows).

Not changed, with reason:
- The store facade (`host_identity_store_read_v1`) and `HostIdentityPlatformV1.read_v1` only re-wrap the same
  `Option<[u8]>` (shared, not copied); the orchestrator callers already move it out and wipe it (milestone_0051).
- `profile_locator_v1` reads only `.profile` leaves (no private key) and is unchanged.

Still unwiped (cannot be reached by a `[u8]` wipe today):
- Windows store: `WindowsJournalStoreV1.read` returns the file as immutable `text`, and `publish` takes
  `bytes_to_text(bytes)`. Those text copies of the private key cannot be wiped without a bytes-based journal API.
- Entropy: `sosix_random_hex` is `crypto_sffi.random_hex` over `extern rt_random_hex -> text?`. The 36 entropy bytes
  (seed + check) exist as immutable hex text; no bytes-returning entropy API exists. Needs a runtime extern; not added.
- Integer locals and limb arrays inside the arithmetic: SHA-512 compression round locals (`i64` values, not arrays);
  `ed25519_scalar.spl` `sc_reduce` / `sc_muladd` (fresh `[u32]` limb arrays per bit step, holding `a`, `r` and their
  products); `ed_scalar_mul` (`[u64]` / `Fe25519` limbs of the accumulator and table points, whose partial values
  depend on the secret scalar, and the per-window `digit`); `_pure_ed25519_clamp`'s per-byte local. Wiping these needs
  a std-wide policy for arithmetic temporaries (every field/scalar op allocates new arrays) and a measured perf budget.
- Native engines may copy or spill values (registers, stack) outside any place Simple code can name. The sha512.spl
  header records that a full-width `i64` stored into an array allocates under the JIT and is never freed; the SHA-512
  state words are full-width, so `secure_zero_i64_slots` zeroes the slots but not those leaked allocations.
- Assumption (not proven by a run): `_ed25519_wipe_u8` / `_ed25519_wipe_i64` take a `mut` parameter and pass it on to
  `secure_zero_*`'s `mut` parameter. SEMANTICS (milestone_0051) covers locals and fields; a re-passed `mut` parameter
  is assumed to stay the parked sole holder, as the existing `host_identity_decode_private_v1(mut bytes)` already does.
- The spec counts prove each wipe ran and read back zero, not that it hit the only copy; sole-holder shape is pinned by
  source needles only.

## Update 2026-11-20 (milestone_0058 ENTROPY BYTES + WINDOWS JOURNAL BYTES; source-authored, NOT_RUN)
Correction: the earlier text said "no bytes-returning entropy API exists". That was wrong. `std.nogc_sync_mut.crypto.
entropy_platform.entropy_platform_bytes(count) -> Result<[u8], text>` already existed over `extern rt_entropy_fill`,
with a C lane (`src/runtime/runtime_native.c` `rt_entropy_fill` -> `rt_random_bytes_c`: `/dev/urandom` read in a
full-read loop with EINTR retry, BCryptGenRandom on Windows, zeroed and NIL on any failure), a Rust runtime twin
(`sffi/random.rs`, scratch buffer wiped), an interpreter lane (`interpreter_extern/random.rs`, zeroize on failure) and
a codegen spec entry. So no runtime extern, header, ABI table entry or clang selfcheck was added: none was needed.
(The C lane uses `/dev/urandom`, not `getrandom(2)`; that is a fact, not changed here.)

Fixed:
- Entropy hex text. `sosix/entropy.spl` now also exports `sosix_random_bytes` (alias of `entropy_platform_bytes`).
  `host_identity_key_generate_v1` draws the 36 seed + check bytes with it, takes the payload out of the Result into a
  sole-holder `var` and overwrites the Result, then calls the new
  `host_identity_key_generate_from_entropy_bytes_run_v1(mut bytes, label)`, which wipes the bytes on every exit (also
  on a wrong length or an all-zero seed, wiped 1). The hex entry is now a thin wrapper kept for regression vectors
  (same refusal codes, `wiped: 0` on invalid hex, 5 on success). Spec (NOT_RUN):
  test/01_unit/app/orchestrator/host_identity_entropy_bytes_v1_spec.spl (ENTBYTES-01..03).
- Windows store text copies. `WindowsJournalStoreV1` gained additive `read_bytes` / `publish_bytes` (publish = no
  replace, operation 0). `read_bytes` keeps `read`'s quota, name, absence and UTF-8 contract, copies into a pre-sized
  `[u8]` (no push), zeroes the native buffer before `rt_free` on every exit and wipes the copy before a UTF-8 refusal.
  `publish_bytes` revalidates UTF-8 and zeroes its native copy before `rt_free`. `identity_windows_read_v1` /
  `identity_windows_publish_v1` use them, so no `text` copy of a key file is made on the Windows store path. The text
  methods and their non-key callers are unchanged. Spec (NOT_RUN):
  test/01_unit/lib/nogc_sync_mut/io/windows_journal_bytes_wipe_v1_spec.spl (JBWIPE-01..04).

Remaining (milestone_0058 scope):
- The text journal methods (`read`, `publish`, `replace`, `compare_replace`, `publish_consumption`) still free their
  native buffers unzeroed and build text. Their callers carry non-key records (leases, WAL CURRENT, receipts), so
  they were left alone.
- Native `rt_windows_journal_read_v1` / `rt_windows_journal_publish_v1` (`src/runtime/platform/
  runtime_windows_journal_store_v1.h`): read writes straight into the caller's buffer; internal staging copies in
  `wj_read_leaf_v1` / `wj_write_v1` were not audited here.
- `entropy_platform.spl` `_entropy_platform_raw` keeps the array in `raw` (`[u8]?`) and `bytes = raw ?? []` while
  building the Result; assumed to share one allocation (no copy), not proven by a run. On its wrong-length refusal
  (a broken provider only) `_entropy_platform_wipe(bytes)` takes a non-`mut` parameter while `raw` still shares the
  allocation, so by the milestone_0051 rule that wipe forks and the provider's bytes survive. Not fixed here: the clean
  fix releases `raw` first, which needs a `nil` store outside `unsafe` (or a reshaped helper) in a module other lanes
  consume. Opus review r1 P2-2.
- Perf (accepted, not a regression of a hot path): `_journal_free_wiped` makes one `volatile_write_u8` FFI call per
  byte. The bytes read wipes `count + 1` on success and the whole `maximum + 1` (65537 for the identity store) on its
  error exits; a native bulk-zero helper would remove the per-byte calls.
- Everything under milestone_0055 "Still unwiped" other than the entropy and Windows items is unchanged (ed25519
  arithmetic temporaries, SHA-512 round locals, engine register/stack copies, the re-passed `mut` parameter
  assumption, which this change also relies on for `host_identity_key_generate_from_entropy_bytes_run_v1`).

