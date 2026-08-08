# `credential_derive_key` is non-deterministic AND wrong under the seed JIT — the credential-store KDF does not derive a key

- **Filed:** 2026-08-08
- **Severity:** CRITICAL (the credential-store KDF is not a function of its
  inputs under the JIT; a key derived at generate time cannot be reproduced)
- **Status:** OPEN. Root cause is a compiler/JIT defect, not a `.spl` spelling
  issue — see "What was tried and REFUTED" below. No source change is shipped
  with this doc, because no candidate edit produced a positive control.
- **Component:** `src/lib/nogc_sync_mut/terminal/credential/store.spl`
  (`credential_derive_key`), seed JIT (Cranelift path)

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

## What was tried and REFUTED

The prevailing theory handed to this lane was that the KDF input path was
corrupted by container spelling — that `list` / `list<i64>` params read elements
shifted left by 3 under the JIT, and only `[T]` is safe. **That theory does not
explain this defect, and its supporting measurements were an artefact.**

1. **The 4-row spelling table came from a stale stdlib.** `bin/simple run`
   resolves `use std.…` **relative to the script's directory**, walking up for a
   `src/lib/`. A probe run from a scratchpad path silently bound to a stale
   `src/lib` copy left there by an earlier lane (blob `fd32d22c`, dated Aug 7,
   the pre-fix `bytes_to_hex(bytes: list)`). Against that tree the probe reported
   `list`/`list<i64>`/`list[i64]` = shifted (diff 455) and `[i64]` = correct.
   Re-run from **inside the repo tree**, with the same probe file and the real
   `src/lib`, **every spelling reads correctly (diff 0)**, including
   `list<list<i64>>`. The shift-left-3 reading is a property of the stale copy,
   not of the deployed toolchain.
2. **Rewriting the KDF path to `[T]` did not fix it.** Changing
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
