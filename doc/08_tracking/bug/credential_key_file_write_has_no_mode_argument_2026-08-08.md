# Secret files are created world/group-readable, then narrowed — no write-with-mode primitive

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 00).

- **Filed:** 2026-08-08
- **Severity:** MED (residual after the 0600 chmod landed)
- **Area:** runtime file I/O / `src/lib/nogc_sync_mut/terminal/credential/store.spl`

## What is wrong

`credential_key_generate` writes the AES-256 credential key with
`rt_file_write_text`, then narrows the file to `0600` with `rt_package_chmod`.
That closes the standing exposure — before 2026-08-08 there was no chmod at all
and the key landed `0664`, group-readable — but it leaves a **race window**:
between the write and the chmod the secret exists on disk at the umask-derived
mode.

The cause is that **no write path in the tree accepts a mode argument**:

| write path | mode used |
|---|---|
| `src/compiler_rust/.../file_io.rs:217` (`fs::write`) | `0666 & ~umask` → `0664` on this box |
| `src/runtime/runtime_native.c:8425` (`open(...)`) | hard-coded `0644` |

Neither exposes `O_CREAT` with a caller-supplied mode, so a caller that needs a
secret file cannot create it restricted; it can only create it loose and then
tighten it.

## Reproduce

```
rm -f /tmp/k && SIMPLE_CREDENTIAL_KDF_COST=4 <generate a key at /tmp/k>
# racing `stat -c %a /tmp/k` during the call can observe 0664 before 0600
```

The final state is `0600` (pinned by
`test/01_unit/lib/terminal/credential_key_derivation_hardening_spec.spl`), so
this is a window, not a persistent exposure.

## Fix

Add a mode-carrying write primitive and route secret writers through it:

- runtime C: `rt_file_write_text_mode(path, content, mode)` →
  `open(path, O_WRONLY|O_CREAT|O_TRUNC, mode)`.
- Rust seed `file_io.rs`: `OpenOptions::new().mode(mode)` under
  `std::os::unix::fs::OpenOptionsExt`.
- Then `credential_key_generate` creates at `0600` directly and the chmod
  becomes a belt-and-braces no-op rather than the only defence.

Adding the extern requires a bootstrap rebuild, which is why the chmod-after
form landed first.

## Related secret-bearing writers to audit under the same fix

A bounded sweep for `.spl` files that both mention secret material and write to
disk surfaced these as worth checking for the same gap (none audited yet):

- `src/lib/nogc_sync_mut/oauth2.spl`, `src/lib/gc_async_mut/oauth2.spl`,
  `src/lib/nogc_async_mut/oauth2.spl` — token persistence
- `src/lib/nogc_async_mut/payment/src/vault/encrypted_vault.spl` — vault file
- `src/lib/editor/00.common/config.spl` — config that may carry credentials

`src/lib/nogc_sync_mut/package/install.spl:126` deliberately sets `0o755` on
installed executables and is not affected.

## See also

- `doc/09_report/lib/crypto/credential_store_aes_cbc_adversarial_review_2026-08-08.md` (finding F3)
- `doc/08_tracking/bug/credential_store_aes_cbc_label_is_actually_ctr_with_deterministic_iv_2026-08-07.md`

## 2026-08-17 verification — runtime lane

**Verdict: STILL OPEN. Confirmed by source; fix is scope-blocked, not disputed.**

Line reference correction: the `open(...)` cited as `runtime_native.c:8425` has
drifted — 8425 is now inside `rt_file_exists_probe_end`. The real hard-coded
mode sites in current source are:

- `src/runtime/runtime_native.c:9654` — `rt_file_write_text_at`: `open(path, O_WRONLY | O_CREAT, 0644)`
- `src/runtime/runtime_native.c:10121` — `rt_file_truncate`: `open(path, O_WRONLY | O_CREAT, 0644)`
- `src/runtime/runtime_native.c:9742-9765` — `rt_core_file_write_data` (backs
  `rt_file_write_text` / `_append` / `rt_file_write_bytes`) uses `fopen(path, "wb")`,
  i.e. `0666 & ~umask`.

The one counter-example proving the primitive is expressible is `:9550`,
`open(temp_path, O_WRONLY | O_CREAT | O_EXCL, 0600)` — a single call site that
hard-codes the restrictive mode rather than accepting one.

So the doc's core claim holds exactly as written: **no write path in the tree
accepts a caller-supplied mode**, and every secret writer must create-loose then
chmod-tight.

**Why this lane did not fix it.** The fix is a three-part change and only the
first part is in this lane's scope (`src/runtime/**`): the runtime primitive
`rt_file_write_text_mode`, the Rust seed's `file_io.rs` `OpenOptionsExt` path
(`src/compiler_rust/**`, another lane), and the routing of
`credential_key_generate` in `src/lib/nogc_sync_mut/terminal/credential/store.spl`
(another lane). Landing the C primitive alone would add an unreachable extern —
dead code by the project's own code-style rule — and, as the doc notes, it needs
a bootstrap rebuild, which was excluded while a stage-3 bootstrap held the host.
**This wants a single owner across all three paths, not a runtime-only patch.**

## 2026-08-17 verification — runtime slice (classified by CONTENT)

**Verdict: STILL OPEN — confirmed live, with corrected line numbers.** The doc
header cites `src/runtime/runtime_native.c:8425`; that is stale. Current source
has TWO hard-coded-0644 creation sites:

```c
src/runtime/runtime_native.c:9654:  int fd = open(path, O_WRONLY | O_CREAT, 0644);
src/runtime/runtime_native.c:10121: int fd = open(path, O_WRONLY | O_CREAT, 0644);
```

so a secret is created world/group-readable and only narrowed afterwards — the
race window the doc describes is real and observable via `stat` during the write.

There is still **no write-with-permission-mode primitive** anywhere in the
runtime. The only near-miss is `file_write_with_mode`
(`src/runtime/simple_core/core_fs.spl:215`, called at :238/:274/:311), whose
`mode_str` is an **fopen mode string** (`"w"`/`"a"`), not a permission bitmask —
it does not address this bug and must not be mistaken for the fix.

Note the one place that already gets this right, as the model for the fix:
`:9550` uses `open(temp_path, O_WRONLY|O_CREAT|O_EXCL, 0600)` (Windows sibling at
:9545). The minimal fix is to thread a mode argument to the two 0644 sites and
default secret writes to 0600.

**Not fixed here, deliberately.** The fix is only meaningful together with its
callers, which live in `src/lib/**` — outside this worker's file slice, where an
edit would be a cross-worker clobber. Adding an uncalled runtime primitive alone
would also violate the "never add unused code" rule. Handing off with the exact
sites above.
