# Lane SMALLFIX — state

Date: 2026-07-28. Binary: `bin/simple` → `bin/release/x86_64-unknown-linux-gnu/simple`
(prints the "Rust-built bootstrap seed only" banner — all verdicts below are seed verdicts).
No commit, no push.

## (1) ssh_kex.spl missing re-export — DONE

`src/os/apps/sshd/ssh_kex.spl` never brought `ssh_sign_exchange_hash` into
scope. Added `use os.apps.sshd.ssh_kex_crypto.{ssh_sign_exchange_hash}` and the
matching `export`.

`test/01_unit/os/apps/sshd/ssh_kex_hostkey_matrix_spec.spl`, A/B against
`git show HEAD:src/os/apps/sshd/ssh_kex.spl`:

| describe | before | after |
|---|---|---|
| ssh-ed25519 host key signing | 10 ex, 8 fail | 10 ex, 0 fail |
| host-key aware KEXINIT builder | 2 ex, 1 fail | 2 ex, 1 fail (pre-existing) |
| rsa-sha2-256 host key signing | 3 ex, 3 fail | 3 ex, 0 fail |
| rsa-sha2-512 host key signing | 3 ex, 3 fail | 3 ex, 0 fail |
| ecdsa-sha2-nistp256 host key signing | 4 ex, 4 fail | 4 ex, 0 fail |
| unknown host key algorithm | 1 ex, 1 fail | 1 ex, 0 fail |
| host_key_set_advertised_algorithms | 5 ex, 0 fail | 5 ex, 0 fail |

`test/02_integration/os/apps/sshd/sshd_production_packet_transcript_spec.spl`:
semantic error (0 run) → **1 example, 0 failures** — the end-to-end session walk
now actually passes.

### newly-revealed genuine failure, fixed

"binds the Ed25519 signature to the full KEX transcript" failed on
`expect(hash_1).to_not_equal(hash_2)`. Root cause is NOT in the sshd source:
`ssh_kex_compute_exchange_hash` declares `client_version: [u8]` /
`server_version: [u8]`, the spec passed `text`, and **the compiler silently
accepts a `text` argument for a `[u8]` parameter and the value contributes
nothing to the digest**. Proven in `build/smallfix_xhash.spl`:
`TEXT differ = false`, `BYTES differ = true`. Production
(`ssh_session_kex.spl:585`) passes real `[u8]`, so the daemon's version binding
is correct. Fixed the spec's `_full_transcript_hash` to call
`rt_text_to_bytes()` (extern already declared in that spec).

### left open

- "encodes the KEXINIT cookie, languages, and reserved trailer at fixed offsets"
  fails identically at HEAD — pre-existing, untouched.
- `test/unit/os/apps/sshd/ssh_kex_hostkey_matrix_spec.spl` is a stale, textually
  divergent mirror (no `rt_text_to_bytes` extern at all); not updated.
- The compiler accepting `text` for a `[u8]` parameter, silently, is a real
  type-checker hole worth its own filing.

## (2) markers.validate() — DONE, three defects not one

Bug doc: `doc/08_tracking/bug/markers_module_unparseable_and_spec_drift_2026-07-28.md`

`markers.validate()` had never run for three stacked reasons:
`MarkerSpec.namespace` made the whole module unparseable (hard "common mistake"
error, 24 sites) → renamed to `ns`; `spec.is_nil()` → `spec == nil`;
`Result.err()/Result.ok()` (not a class in Simple) → `Err()/Ok()`.

`test/01_unit/os/kernel/logging/marker_wire_format_spec.spl`: 0 examples run
(module parse error) → **8 examples, 4 failures**. `validate()` executes and
correctly rejects a level-prefixed marker.

Left open (need the wire-format owner): `[BOOT]` vs `[boot]` case mismatch (2
failures) and `NAMESPACE_BOOT` not existing in the module (2 failures). Both
recorded in the bug doc; not patched blind because the case is part of the
serial wire format a boot-log parser reads. markers.spl has no production
callers — nothing could import it.

## (3) SdnValue insert — DIAGNOSED, cannot be fixed at this layer

Bug doc: `doc/08_tracking/bug/enum_payload_dict_copied_on_function_return_2026-07-28.md`

Not the two-hop mutating-chain class and not a plain value-semantics copy.
`insert` was a literal no-op (`case Dict(_): true`), and the reason it had to be
is that **an enum's collection payload is copied at the function-return
boundary**. Probe table (`build/smallfix_probe3.spl`): enum built in the
caller's own frame → write persists (7); enum returned from a static ctor →
write lost (-1), whether the ctor uses a dict literal or a named local, and
whether the write goes through a method or an inline match.

Also ruled out: `mut self` + `self = ...` reassignment (not visible to caller),
and boxing the dict in a class inside the payload (same result).

Changed `insert` to write through a `mut`-parameter helper (`_sdn_dict_put`) —
the only form the interpreter propagates at all — plus a comment stating exactly
when it does and does not persist. `"get by key from dict"` in
`test/01_unit/lib/common/sdn_coverage_spec.spl` is **still RED** (51 examples, 1
failure, unchanged before/after). It was NOT turned green: doing so would need
either a compiler fix or changing `insert`'s bool return contract, which four
other examples in the same file assert on. The assertion was not touched and the
spec was not rewritten to dodge the defect.
