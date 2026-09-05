# sshd_regression_tests — state

Status: DONE (tests written, deliberate-red calibrated, green re-verified)
Date: 2026-07-28
Engine: **interpreter only** (`bin/simple run`, Rust seed). Any spec importing
`os.apps.sshd.sshd` pulls `os.crypto.ed25519`, which cannot JIT-lower
(`Unknown type: u128`). No native/JIT claim is made for either spec.

## Scope

Regression tests for two sshd defects that were reported and found already
fixed by a concurrent lane, but which had no test:

1. daemon advertised `ssh-ed25519` even when config disabled it
   (`advertise_ed25519` / `advertise_ed25519_host_key` plumbing in `sshd.spl`)
2. interactive shell bridge never executed commands — banner + prompt only
   (`ssh_remote_shell.spl` char-slice rewrite)

`src/os/apps/sshd/**` was NOT modified (temporarily broken for deliberate-red,
then restored byte-identical — verified by `diff -q` against an out-of-tree
backup in `/tmp/sshd_regr_backup/`).

## Files

- `test/01_unit/os/apps/sshd/sshd_host_key_advertise_policy_spec.spl`
  (17 examples across 4 describes; the `SSHD never negotiates a disabled host
  key algorithm` describe — 6 examples — was added by this lane)
- `test/01_unit/os/apps/sshd/ssh_session_shell_spec.spl`
  (15 examples; the two absolute-transcript examples were added by this lane)

## Results (interpreter)

sshd_host_key_advertise_policy_spec.spl
- SSHD host key advertisement follows config — 4 examples, 0 failures
- SSHD host key policy fails closed — 5 examples, 0 failures
- SSHD never negotiates a disabled host key algorithm — 6 examples, 0 failures
- SSHD certificate-aware host key list follows config — 2 examples, 0 failures

ssh_session_shell_spec.spl
- SSH shell session bridge — 15 examples, 0 failures

## Deliberate-red calibration

RED 1 — gate broken (`ed25519_seed: if advertise_ed25519: ... else: nil`
replaced by unconditional `ed25519_seed`, both test hooks + the live
`build_host_keys_for_session`): 10 of 17 advertise examples went red
(4/3, 5/2, 6/4, 2/1 per describe). Reverted; re-ran 17/17 green.

RED 2 — bridge broken (`self._execute_line(...)` removed from
`feed_remote_input`, i.e. prompt-only): 8 of 15 shell examples went red.
Reverted; re-ran 15/15 green.

## Coverage limits (explicit)

- Unit-level only. Both specs exercise pure/policy surfaces and the in-memory
  `SshRemoteShell`. They do NOT cover the encrypted session state machine,
  channel/PTY handling, or a real SSH client handshake — that rests on the
  QEMU gate (`test/03_system/os/ssh_live_login_in_qemu_spec.spl`).
- Only 5 of 27 sshd source files carry an `@cover` target; these specs add no
  new `@cover` annotation, so coverage accounting is unchanged.
- The negotiation examples drive `ssh_negotiate_algorithms` against a
  reconstructed client proposal, not a captured wire transcript from OpenSSH.
- Interpreter-only. JIT/native behaviour of this code is unverified here.

## Findings to report (NOT patched by this lane)

1. `SshDaemon.host_key_policy_satisfiable()` (`sshd.spl:587`) exists and is
   documented as the fail-closed gate, but `start()` (`sshd.spl:432`) never
   calls it — it only logs which self-test path it took and then binds. The
   fail-closed policy is therefore tested at the function level but is not
   wired into the daemon's startup refusal path.
2. `SshDaemon.build_host_keys_for_session()` (`sshd.spl:580`) hard-nils
   `rsa_pkcs8` / `rsa_public_blob` / `ecdsa_p256_pkcs8` by design (RV64 live
   lane comment). So the production KEXINIT never carries RSA regardless of
   configured RSA material, while
   `test/02_integration/os/apps/sshd/sshd_production_session_kexinit_spec.spl`
   asserts `rsa-sha2-256,rsa-sha2-512` in the disabled-ed25519 case. Those two
   cannot both be current — the integration spec looks stale relative to the
   live selector. Not investigated further here.
3. Weak pre-existing example: `"returns pwd output through the shell bridge"`
   stayed GREEN under RED 2, because `"/"` also occurs in the prompt string.
   The added absolute-transcript example is what actually pins pwd.
