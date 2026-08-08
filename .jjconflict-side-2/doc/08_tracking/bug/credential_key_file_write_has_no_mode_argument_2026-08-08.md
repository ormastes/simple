# Secret files are created world/group-readable, then narrowed — no write-with-mode primitive

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
