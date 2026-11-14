# Native devhub reports a missing SQLCipher store as `corrupt-source`

**Status:** OPEN
**Found:** 2026-11-14
**Severity:** P2 — wrong error class, native only; still fails closed (exit 2, nothing leaked)

## Symptom

With the messenger config pointing at a file that does not exist:

```
interpreter: {"target":"","action":"rooms","status":"error","code":2,"error":"config_error: source-unavailable","warnings":[]}
native:      {"target":"","action":"rooms","status":"error","code":2,"error":"config_error: corrupt-source","warnings":[]}
```

`src/app/devhub/messenger/adapter/db_common.spl` maps `StoragePortError.Io` to
`source-unavailable` and `StoragePortError.CorruptSource` to `corrupt-source`, so
natively either the open of a missing file does not produce `Io` (it yields an
empty read that later fails as corrupt), or the variant is matched wrongly.

## Repro

Seed build-commit `97728d94d5f1`, Windows, llvm-mingw 20260922; native devhub
built as in `devhub_native_sqlcipher_history_truncated_at_25_rows_2026-11-14.md`.

```
DEVHUB_NATIVE_BIN=<abs>/build/nb/devhub.exe simple test test/03_system/app/devhub/messenger/messenger_read_verbs_damaged_store_spec.spl
```

```
✗ reports the source as unavailable without a crash or a path dump
    expected false to equal true
Results: 7 total, 6 passed, 1 failed
```

Interpreted: `Results: 7 total, 7 passed, 0 failed`. The other six damaged-store
cases (flipped byte, truncated file, plaintext file) agree on both engines.
