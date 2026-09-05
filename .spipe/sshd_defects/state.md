# sshd_defects — lane SSHDFIX

Two real defects in `src/os/apps/sshd/` (pure-Simple SSH daemon), found by lane
SSHNAT (read-only survey), reproduced and fixed here.

## (a) SECURITY: disabled host-key algorithm still advertised in KEXINIT

**Reproduced.** `build/sshdfix_repro/repro_kexinit.spl`, before fix:

```
ENABLED  algos=[ssh-ed25519]
DISABLED algos=[ssh-ed25519] seed_nil=true    <-- BUG
RSAONLY  algos=[rsa-sha2-256,rsa-sha2-512]
```

`SshDaemon.set_advertise_ed25519_host_key(false)` correctly nils
`HostKeySet.ed25519_seed` (`sshd.spl` `build_host_keys_for_session`,
`seed_nil=true` above), but three list builders in
`src/os/apps/sshd/ssh_kex_primitives.spl` **failed open** to a hardcoded
default when the resulting set was empty:

- `host_key_set_advertised_algorithms` — `if algos.len() == 0: algos = "ssh-ed25519"`
- `host_key_algorithms_with_certificates` — same trailing default
- `_push_host_key_algorithms` (the byte-wire path used by
  `ssh_build_kexinit_for_host_keys_and_certs`) — final fallthrough
  `_push_ssh_ed25519(buf)`

So a client could negotiate `ssh-ed25519` against a server whose operator had
switched it off.

**The bug was spec-blessed.** `test/01_unit/os/apps/sshd/ssh_kex_hostkey_matrix_spec.spl`
carried `it "empty set defaults to ssh-ed25519"` asserting the fail-open value.
That `it` is now `"empty set advertises nothing (fail closed, never a default
algorithm)"` with oracle `== ""`.

**Fix (fail closed):**
- all three builders now yield an empty list / empty name-list when nothing is
  configured. `ssh_negotiate_algorithms` (`ssh_transport.spl:513`) already
  rejects an empty server list with `Err("no matching host key algorithm")`, so
  an empty advertisement is a genuine wire-level refusal, not a soft failure.
- new `host_key_set_has_any_algorithm(host_keys) -> bool` in
  `ssh_kex_primitives.spl`.
- new `SshDaemon.host_key_policy_satisfiable()` and an explicit refusal at the
  top of `SshDaemon.start()`:
  `Err("sshd: no host key algorithm enabled")` — the daemon refuses to serve
  rather than advertising a default. Certificates count toward satisfiability.
- test hook `sshd_host_key_policy_satisfiable_for_test`.

After fix: `DISABLED algos=[]`, `ENABLED algos=[ssh-ed25519]`, `RSAONLY` unchanged.

### Algorithm-list audit (KEX / cipher / MAC)
Checked the same class in `ssh_build_kexinit_for_host_keys_and_certs`
(`ssh_kex.spl` — lane SMALLFIX's file, not edited here):

| list | source | config-driven? |
|---|---|---|
| host key | `HostKeySet` | yes — **was the bug, now fixed** |
| KEX | hardcoded `curve25519-sha256,ext-info-s,kex-strict-s-v00@openssh.com` | no config knob exists |
| cipher | hardcoded aes256-gcm (+aes128-gcm on the no-cert path) | no config knob exists |
| MAC | hardcoded | no config knob exists |

Only host-key has a config surface, so only it can diverge from config. **Not
fixed, reported:** the two branches of that one function disagree on the MAC
list — the certificate path advertises
`hmac-sha2-512-etm,hmac-sha2-256-etm,none` while the no-certificate path
advertises `none` only. Under AES-GCM the MAC field is ignored so this is not a
live weakness, but the divergence is unintentional and lives in a file this
lane does not own.

## (b) Interactive shell bridge never executed commands

**Reproduced.** `build/sshdfix_repro/repro_shell.spl`, before fix:

```
BANNER=[SimpleOS Shell v0.2 ... user@simpleos:/# $ ]
AFTER_ECHO=[]        <-- "echo ssh" produced nothing at all
AFTER_WHOAMI=[]
```

**Not a wire-up gap, not a lost mutation.** All three suspected shapes were
tested and cleared in `build/sshdfix_repro/repro_micro.spl` — direct `me`
write, `me` write inside a loop, nested `me`→`me` write, and drain-through-`fn`
all persist correctly.

**Root cause is a language-level defect**, isolated in
`build/sshdfix_repro/repro_char.spl`: iterating a `text` with `for ch in s`
yields char values that compare **false against every char literal** and whose
`.to_i64()` is **0**:

```
i=0 ch_i64=0 is_nl=false is_cr=false
i=1 ch_i64=0 is_nl=false is_cr=false
i=2 ch_i64=0 is_nl=false is_cr=false   <-- s = "ab\n"
```

(String-interpolating `{ch}` still reproduces the right character, so the
corruption is in the char *value*, not the iteration.) In
`ssh_remote_shell.spl` `feed_remote_input`, `ch == '\n'` was therefore never
true, so no line was ever terminated, `_execute_line` never ran, and every
byte accumulated silently into `input_line`. The session returned banner +
prompt and nothing else.

**Fix:** `feed_remote_input` now walks the input by single-character text slice
(`input[i:i + 1]`, compared against `"\n"` / `"\r"`), the idiom verified working
in `repro_char2.spl`. `take_remote_output` also changed `fn` → `me` since it
mutates (behaviour was already correct; this is intent-correctness only).

After fix: `echo ssh` → `ssh` + prompt; `whoami` → `root` + prompt.

**Upstream defect not filed by this lane** (out of scope): `for ch in <text>`
producing dead char values is a compiler bug affecting any `.spl` that scans
text this way. Only `ssh_remote_shell.spl` used that shape inside
`src/os/apps/sshd/`.

## Evidence boundary — what this does NOT prove

- Engine: **interpreter only** (`bin/simple run`). Every sshd spec that touches
  `os.crypto.ed25519` is interpreter-only anyway (`Unknown type: u128` blocks
  JIT lowering — lane U128JIT). "Green on both engines" would be a false claim.
- Unit-level only. The session state machine still rests on the QEMU gate, and
  only 5 of 27 sshd files carry an `@cover` target. No live `ssh` client was
  driven against the fixed daemon in this lane, so (b) is proven at the
  `SshRemoteShell` bridge, not end-to-end over a real SSH channel.
- (a)'s daemon-level refusal is proven through the `..._for_test` hook and by
  reading `start()`; `start()` itself was not executed (it binds a socket).
- Board-runnable: unchanged: both fixes are pure `.spl` logic in the same files
  the QEMU/board lane already builds; no new host dependency introduced.
