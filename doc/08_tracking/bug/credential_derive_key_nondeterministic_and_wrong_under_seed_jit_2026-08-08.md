# `credential_derive_key` is non-deterministic AND wrong under the seed JIT — the credential-store KDF does not derive a key

- **Filed:** 2026-08-08
- **Severity:** CRITICAL (the credential-store KDF is not a function of its
  inputs under the JIT; a key derived at generate time cannot be reproduced)
- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (triage shard 00).
  bare-name symbol collision on `text_to_bytes` reached from *inside*
  `eksblowfish_setup`, resolved differently depending on which modules the
  CALLER pulled in. Fixed in `.spl` with a RED→GREEN→RED control against an
  engine-independent reference oracle.
- **Component:** `src/lib/common/bcrypt/types.spl` (`text_to_bytes`, the actual
  root cause), `src/lib/nogc_sync_mut/terminal/credential/store.spl`
  (`credential_derive_key`), seed JIT (Cranelift path)

## RESOLUTION (2026-08-08)

### The "non-determinism" was mis-characterised

Repeated calls to `credential_derive_key` in one process are **stable** — the
within-process drift reported in the Symptom table did not reproduce. What is
real, and what produced those varying numbers, is that the derived key depends
on **which modules the calling program imports**, and (before this fix) on
**which engine runs it**. A probe whose import list changes gets a different
key from the same passphrase and salt. That is just as fatal for reproducibility
as true non-determinism, and it is why successive probes in the earlier lanes
disagreed with each other.

### The oracle that made this tractable

The earlier lanes used *self-consistency* (call twice, compare) as the oracle.
That cannot distinguish "correct" from "consistently wrong", and it is why two
candidate fixes moved the numbers without ever proving anything.

The oracle used here is an **in-probe replica**: the exact `credential_derive_key`
algorithm re-implemented inside the probe file over the same library primitives
(`eksblowfish_setup`, `blowfish_encrypt_block`, `hkdf_sha256`). It scores
**74807 in both engines and every module set** — it is engine-independent and
caller-independent, so it is a trustworthy reference. Supporting known-answer
checks: `hkdf_sha256` passes RFC 5869 Test Case 1 in both engines, and the
stage-1 bcrypt `ikm` replica agrees byte-for-byte across engines.

Against that reference, at the origin blobs:

| module set | engine | `credential_derive_key` | reference |
|---|---|---|---|
| minimal caller | JIT | 81572 / 44766 | 74807 |
| minimal caller | interpreter | 81572 | 74807 |
| caller also imports bcrypt+hkdf+aes | JIT | 63367 | 74807 |
| caller also imports bcrypt+hkdf+aes | interpreter | 73924 | 74807 |

Every cell is wrong, and they disagree with each other by engine AND by caller.

### Root cause

`eksblowfish_setup` (`src/lib/common/bcrypt/key_derivation.spl:273`) calls
`text_to_bytes(password)`. It imports that name via `use std.bcrypt.types.*` —
a module path that **does not exist** (`src/lib/bcrypt/` is absent; the real
tree is `src/lib/common/bcrypt/`). Unresolved `use` is warning-only, so the
call falls back to bare-name resolution across the co-compiled set, where
`text_to_bytes` has **three definitions with two different return types**
(`[i64]` in `bcrypt/types.spl` and `crypto/types.spl`, bare `list` in
`aes/utilities.spl`, `[u8]` in `base_encoding`). The compiler warns about
exactly this and says the fallback "may still dispatch to the wrong one".

Whether the *correct* `[i64]` definition wins depends on module ordering, which
depends on the caller's imports. When the wrong one wins, the password bytes
entering the bcrypt key schedule are wrong (a bare-`list` value read across a
module boundary reads its elements shifted left by 3), so the whole key is wrong.

The discriminating experiment: with the library unchanged, adding
`use std.common.bcrypt.key_derivation…` **to the caller** flips the result from
81572 to the correct 74807. Adding `hkdf` or `aes` imports instead does not.

### The fix

Applied the remedy the compiler warning itself prescribes — remove the
ambiguity rather than hope the fallback picks correctly:

1. `src/lib/common/bcrypt/types.spl` — `text_to_bytes` renamed to
   `bcrypt_text_to_bytes` (unique name, no longer in the collision set).
   Callers updated in `key_derivation.spl` and `hash.spl`. **This is the fix
   that closes the defect**; the rest is hardening.
2. `src/lib/common/aes/utilities.spl` — `text_to_bytes` return type bare
   `list` → `[i64]`, matching the already-landed `bytes_to_hex`/`bytes_to_text`
   fixes.
3. `store.spl` — KDF path respelled to `[T]` (`salt`, return type,
   `magic_words`, `ikm`, plus `credential_key_file_salt` and
   `credential_load_key` return types); `use std.bcrypt.…` corrected to
   `use std.common.bcrypt.…`; HKDF info bytes built by a uniquely-named local
   `credential_kdf_info_bytes()` so the KDF never rides the shared
   `text_to_bytes` dispatch at all.

Fixes 2 and 3 alone do **not** close the defect (measured: values move, caller
dependence persists). Fix 1 is load-bearing.

### Control (RED → GREEN → RED)

Marker-free ship blobs, probe run from inside the repo tree, blob SHAs verified
before and after every arm:

| arm | JIT | interpreter |
|---|---|---|
| RED (origin blobs) | 81572 | 81572 |
| GREEN (fix applied) | **74807** | **74807** |
| RED again (reverted to origin) | 81572 | — |

And with the fix applied, all four cells of {minimal caller, rich caller} ×
{JIT, interpreter} return **74807** — engine-independent and caller-independent,
matching the reference. Repeated calls are stable. `credential_key_generate` →
`credential_encrypt` → `credential_decrypt` round-trips exactly.

### Note on the two defects

The container-spelling corruption and this dispatch defect are **independent**.
Respelling the whole KDF path to `[T]` (fix 3) left the caller dependence fully
intact; renaming the colliding helper (fix 1) removed it. They were entangled
only in the sense that both were corrupting the same key.

## Symptom

Calling `credential_derive_key(passphrase, salt, cost)` twice, in one process,
with byte-identical arguments, returns two DIFFERENT 32-byte keys — and neither
of them is the key the interpreter derives from the same inputs.

Measured with an arithmetic oracle (position-weighted checksum, never a printed
element — print-only probes are worthless for this defect family):

| engine | call 1 checksum | call 2 checksum | delta |
|---|---|---|---|
| interpreter (`SIMPLE_EXECUTION_MODE=interpret`) | 72527 | 72527 | **0** |
| seed JIT (default `bin/simple run`) | 69918 | 72292 | **-2374** |

The JIT numbers are stable run-to-run (reproduced across repeated runs), so the
defect is *call-order dependent*, not randomised: within a process, the Nth call
to `credential_derive_key` returns a different key from the (N-1)th. The
interpreter value (72527) matches neither JIT value, so **both JIT results are
wrong**, not merely inconsistent.

## Why this matters

`credential_key_generate` derives the key, then stores the FINAL key bytes in
`~/.simple/credential_key` (v2 format `v2:<hex_salt>:<hex_key>`). Because the
final bytes are stored, day-to-day decryption still works. But:

- The stored key is **not** the bcrypt→HKDF derivation of (passphrase, salt).
  The documented KDF contract in `credential_derive_key`'s own docstring is not
  what the file contains.
- **Regeneration cannot reproduce the install's key.** The recorded salt exists
  precisely so that re-running `credential_key_generate` with the same
  passphrase on the same install reproduces the same key. It does not: the next
  call returns a different key. Every credential encrypted under the old key
  becomes undecryptable.
- The key's relationship to the passphrase is severed, so passphrase strength no
  longer bounds key strength in the way the design assumes.

## Localisation — every named callee is individually deterministic

Each component was probed separately, under the JIT, in the same module set:

| probe | result |
|---|---|
| `eksblowfish_setup(pw, salt, 4)` twice, all 5 state rows compared | delta **0** (deterministic) |
| `blowfish_encrypt_block(l, r, state)` twice on the same state | delta **0** (deterministic, and does not mutate the state) |
| `hkdf_sha256(salt, ikm, info, 32)` three times | delta **0**, **0** (deterministic) |
| `hex_to_bytes(hex)` value vs an `[i64]` literal of the same bytes | delta **0** (byte values identical) |
| `credential_derive_key(pw, salt, 4)` three times | delta **-7639**, **-10687** (BROKEN) |

So the composite is non-deterministic while every part of it is deterministic.
That is the shape of a codegen/dispatch defect in the composed frame, not a
logic bug in any one function.

**Caveat on that table:** each callee was probed by calling it twice *in
isolation*, with no intervening `credential_derive_key` call. So it establishes
determinism for repeated-call-in-isolation only — it does NOT rule out that the
192 `blowfish_encrypt_block` invocations inside one derive leave residue that
perturbs the next derive. The obvious next probe is to call `eksblowfish_setup`,
then run a full `credential_derive_key`, then call `eksblowfish_setup` again with
the same arguments and compare.

## Likely mechanism (not yet proven)

Compiling the module set that `store.spl` pulls in emits, from the compiler
itself:

```
warning: public function `text_to_bytes` has 3 co-compiled definitions with 3
differing signatures ((text)->list<i64> vs (text)->[i64] vs (text)->list); JIT
call sites resolve by exact arg-type match (mangled `$dupN` variants), falling
back to the last definition when types are ambiguous — a fallback hit may still
dispatch to the wrong one.
[compiler_cross_module_private_symbol_collision]
```

The same warning fires for `bytes_to_hex` (3 definitions, 2 signatures) and
`compress_block` (2 definitions, 2 signatures). An ambiguous-dispatch fallback
that resolves differently at different call sites is consistent with the
observed call-order dependence. This is a hypothesis: substituting the
`text_to_bytes` call out of the KDF path (see below) did NOT fix it, so if this
is the mechanism it is acting through one of the other colliding symbols.

## CORRECTION (2026-08-08, same day): the container-spelling defect is REAL

An earlier revision of this doc claimed the container-spelling defect was
refuted outright. **That claim was wrong and is withdrawn.** It over-generalised
from a probe that measured the wrong thing. The corrected finding:

**The `list` / `list<i64>` element-read corruption is real, but only for
parameters of functions called ACROSS A MODULE BOUNDARY. A `list`-spelled
parameter on a function defined in the same file as its caller reads correctly.**
That cross-module/same-file distinction is the discriminating condition, and it
is what the withdrawn claim missed: the probe that reported "every spelling is
fine" declared its `list`-param functions *inside the probe file*, so it never
exercised the failing case at all.

Re-measured with markers planted in the library files and held present through
every arm (so edit-visibility is proven *during* the toggle, not merely before
it), cwd = repo root, single variable = the parameter spelling:

| arm | `bytes_to_hex` / `bcrypt_encode_base64` param | AES roundtrip | bcrypt `mismatch_count` | local same-file `list` param |
|---|---|---|---|---|
| 1 | `list` / `list<i64>` | **BROKEN** `0088109820a8…` | **15** | 0 (correct) |
| 2 | `[i64]` / `[i64]` | ok, exact identity | **0** | 0 (correct) |
| 3 | `list<i64>` / `list<i64>` | **BROKEN** | **15** | 0 (correct) |

Markers `recon_marker_5501` (aes) and `recon_marker_9931` (bcrypt) printed their
sentinel values in all three arms, so every arm is known-live. RED→GREEN→RED.
The bcrypt `mismatch_count` of 15 reproduces the independently-measured value
from the bcrypt lane's own probe (landed `5d8e53fa16e`), from a different probe
file and a different oracle.

Consequences for the rest of this doc:

- `list<i64>` is fully typed and breaks **identically** to bare `list` — the
  original guidance ("only `[T]` is safe") stands for cross-module params.
- The bcrypt-tree and `aes/utilities.spl` `[i64]` fixes are correct and should
  stay.
- One thing remains **unreproduced**: an early probe run from a scratchpad path
  reported diff 455 for *same-file* `list` params. In-repo, same-file params
  read correctly under every module set tried. That reading is not explained and
  should not be relied on.
- **Still open for the KDF path specifically:** `credential_derive_key` takes
  `salt: list[i64]` and `credential_key_file_salt` returns `list[i64]`, and
  `hex_to_bytes` returns bare `list` — all consumed across module boundaries.
  Under the corrected model these are exactly the failing shape. They were
  toggled during the investigation below without fixing the *non-determinism*,
  but that does not clear them of the *corruption* defect; they warrant a
  dedicated re-test with the marker-during-toggle method.

## What was tried, and what that ruled out

The container-spelling theory (see the CORRECTION above — it is real, and the
"refuted" framing here is withdrawn) does not by itself explain the
**non-determinism**, which is the finding this doc is about:

1. `bin/simple run` resolves `use std.…` **relative to the script's directory**,
   walking up for a `src/lib/`. A probe run from a scratchpad path silently
   bound to a stale `src/lib` copy left there by an earlier lane (blob
   `fd32d22c`, dated Aug 7, the pre-fix `bytes_to_hex(bytes: list)`). This is a
   real and reusable hazard — it is how an earlier lane measured a live-looking
   result against dead code — but it is **not** grounds for dismissing the
   spelling defect, which reproduces in-repo (CORRECTION above).
2. **Rewriting the KDF path to `[T]` did not fix the non-determinism.** Changing
   `credential_derive_key`'s `salt: list[i64] -> [i64]`, its return type,
   `magic_words: list[list[i64]] -> [[i64]]`, and `ikm: list[i64] -> [i64]`
   changed the returned values but left the call-order dependence intact
   (deltas moved from -7639/-10687 to 1678/-2504). Reverted.
3. **Building the HKDF info bytes inline**, to keep the 3-way-overloaded
   `text_to_bytes` off the KDF path, changed nothing (deltas identical at
   1678/-2504). Reverted.

Because no candidate edit produced a positive control (RED→GREEN→RED), nothing
was shipped. Both files are at their origin blobs:
`src/lib/nogc_sync_mut/terminal/credential/store.spl` = `3f4a22f5`,
`src/lib/common/aes/utilities.spl` = `7eef6661`.

## Method notes for whoever picks this up

- **Edit-visibility must be proven first, and it is easy to get wrong.** Because
  stdlib resolution is script-dir-relative, a probe placed outside the repo tree
  binds to whatever stale `src/lib` happens to be above it and your edits are
  silently ignored. A hard `return "SABOTAGE_MARKER_7731"` inserted at the top of
  `bytes_to_hex` was **invisible** from a scratchpad path and **visible** from
  `build/kdfprobe/` inside the repo. Always sabotage first, from the exact path
  you intend to measure from.
- **Prove visibility DURING the toggle, not once beforehand.** Keep a marker
  function in the edited library file and print it in *every* arm of the A/B.
  Proving visibility once and then measuring lets a later arm silently bind
  elsewhere. This is the method that settled the CORRECTION above; the withdrawn
  claim came from the weaker prove-once-then-measure design.
- **Test the failing shape, not a convenient stand-in.** The withdrawn claim
  measured `list`-spelled params on functions declared *inside the probe file*.
  Same-file params are not affected. The defect only appears across a module
  boundary, so the probe must call a real library function.
- **The stale `scratchpad/src/lib` tree is a live footgun** for every lane that
  runs `bin/simple run` on a scratchpad script. It is the direct cause of the
  mis-scoped spelling table above.
- **Print-only probes prove nothing** for this defect family; assert
  arithmetically against a second value.
- **`bin/simple` here is the Rust bootstrap seed** (it says so on startup), and
  `bin/simple test` is structurally blind to this bug because the interpreter is
  correct. Measure under the JIT and compare against
  `SIMPLE_EXECUTION_MODE=interpret` as the reference.

## Reproduction

From inside the repo tree (the location matters), a probe that imports
`std.nogc_sync_mut.terminal.credential.store.{credential_derive_key}`, builds a
16-byte `[i64]` salt, calls `credential_derive_key("pw", salt, 4)` twice, and
compares a position-weighted checksum of the two results. Under the default JIT
the two checksums differ; under `SIMPLE_EXECUTION_MODE=interpret` they are
equal, and equal to neither JIT value.

## Related

- `doc/08_tracking/bug/credential_store_key_and_salt_corrupted_by_list_param_hex_2026-08-08.md`
- `doc/08_tracking/bug/credential_key_generate_random_hex_length_reads_shifted_2026-08-08.md`
- `doc/08_tracking/bug/rt_package_chmod_family_fails_from_jit_key_left_world_readable_2026-08-08.md`
