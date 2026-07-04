# Native rv64 entry-closure drops a file-local `fn` body → undefined symbol at link

- **Id:** selfhosted_native_local_fn_body_dropped_2026-06-15
- **Status:** Open
- **Severity:** P2 (forces a source workaround in the rv64 sshd lane; risks
  silent symbol drops in any native baremetal module with a wildcard import)
- **Found:** 2026-06-15 (rv64 web-server gate verification; FR-5 of
  `rv64_web_gate_arm64_import_leak_and_storage_2026-06-15`)
- **Component:** compiler / native codegen (`--entry-closure`, LLVM backend),
  baremetal `rv64-base` boot closure
- **File:** `src/os/apps/sshd/ssh_session.spl`

## OBSERVED (confirmed from git history)

A file-local helper in `ssh_session.spl`:

```simple
extern fn serial_println(msg: text)

fn log_raw_println(msg: text):
    serial_println(msg)
```

was DEFINED and USED in the same file, yet was **not emitted** for the riscv64
native build. `ld.lld` reported the mangled name undefined for the `rv64-base`
`--entry-closure` link from `boot.spl`:

```
undefined symbol: os__apps__sshd__ssh_session__log_raw_println
  defined at ssh_session.spl:52, referenced at :491 (same file)
```

The single caller was:

```simple
serial_println("[sshd-session] disconnect payload={_bytes_to_hex(msg)}")
log_raw_println("[sshd-session] disconnect payload={_bytes_to_hex(msg)}")  # ← dropped fn
```

i.e. the wrapper call duplicated the `serial_println` line directly above it.

- **Interpreter mode was fine** — the symptom is native-emission-specific.
- The extern `serial_println` itself was NOT dropped (it is referenced and linked
  everywhere else in the file); only the local Simple `fn` body went missing.

### Workaround applied (landed)

Deleted the dead `log_raw_println` wrapper and its sole caller (the caller was a
duplicate of the `serial_println` line immediately preceding it, so no behavior
was lost). After deletion the link no longer references the missing symbol.

Commits touching this in `ssh_session.spl` on 2026-06-15 (e.g.
`e2341c5fd4def9781ba69ac29201c005c8dd6e5d`, `742c1f73aa109db160d33adfac101d5f7d4d6dc7`)
show the exact removed lines:

```diff
-fn log_raw_println(msg: text):
-    serial_println(msg)
...
-        log_raw_println("[sshd-session] disconnect payload={_bytes_to_hex(msg)}")
```

## HYPOTHESIS (suspected root cause — NOT yet proven)

A short-named local `fn` that **collides with a wildcard-imported name** can have
its body silently dropped in the native entry-closure codegen path, so the call
lowers to an unresolved symbol instead of the local body.

**Supporting evidence (strengthens, does not prove):** `ssh_session.spl`
wildcard-imports three sibling modules at the top of the file:

```simple
export use os.apps.sshd.ssh_session_kex.*
export use os.apps.sshd.ssh_session_auth.*
export use os.apps.sshd.ssh_session_channel.*
```

and `ssh_session_kex.spl:27` ALSO defines a function with the **same name and
signature**:

```simple
# ssh_session_kex.spl
extern fn serial_println(msg: text)
fn log_raw_println(msg: text):
    serial_println(msg)
```

So in the flattened native module two `log_raw_println(msg: text)` definitions
were in scope at once: the file-local one and the one pulled in via
`export use ...ssh_session_kex.*`. A name collision between a file-local `fn` and
a wildcard-imported `fn` of identical name/signature is a plausible trigger for
the emitter dropping the local body (and resolving the call to the import, or to
nothing). This was NOT a collision with the `serial_println` extern — the
colliding name is another local `fn log_raw_println` in a wildcard-imported
sibling module. (`log_raw_println` is a common helper name — defined in ~10 files
repo-wide, including `ssh_session_helpers.spl:29`, also imported here.)

Unverified: whether the collision is the actual cause, or whether the local-fn
emission gap reproduces WITHOUT any colliding import. See repro below.

## Minimal repro sketch (to confirm/refute the hypothesis)

Two probes for a native `--entry-closure` baremetal build:

**A. Collision present (matches observed shape):**

```simple
# mod_b.spl
extern fn serial_println(msg: text)
fn log_raw_println(msg: text):
    serial_println(msg)

# mod_a.spl  (entry-reachable)
export use mod_b.*
extern fn serial_println(msg: text)
fn log_raw_println(msg: text):       # same name+sig as wildcard-imported one
    serial_println(msg)
fn entry():
    log_raw_println("hi")            # expect: undefined symbol at link (native)
```

**B. No collision (control):**

Same as A but with NO `export use mod_b.*` and a uniquely-named local fn. If B
links cleanly and A fails, the wildcard-import collision is confirmed as the
trigger. If A also links cleanly, the original drop has a different cause and this
doc's hypothesis is refuted.

Expectation per OBSERVED: interpreter mode passes both; only native A fails.

## Notes

- Discovered while diagnosing the rv64 web gate; tracked there as FR-5
  (`rv64_web_gate_arm64_import_leak_and_storage_2026-06-15`).
- Build was NOT run while writing this doc (a build was already in progress).
