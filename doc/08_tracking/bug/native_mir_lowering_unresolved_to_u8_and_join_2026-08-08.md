# native-build: MIR lowering has no `to_u8` or `join` — the typed crypto path cannot be built natively

**Filed:** 2026-08-08 · **Severity:** high (blocks native verification of landed
security fixes; not a wrong-answer bug but a cannot-build bug) · **Lane:** pure-Simple
`native-build` (bare-positional entry, i.e. the real self-hosted `CompilerDriver`, not
the `--entry` path that delegates to the Rust runtime).
**Interpreter and seed JIT: both CORRECT.** Only native codegen fails.

## Summary

Two method calls are unimplemented in MIR lowering and abort the native build:

```
error: MIR lowering error: unresolved method call: to_u8
error: MIR lowering error: unresolved method call: join
```

This is **not** a wrong-value defect. The build fails outright (`RC=1`, no binary), so
any code on these paths simply cannot be exercised under native codegen.

## Minimal reproduction (dependency-free — no stdlib crypto involved)

`.nvprobe2/mir_gap.spl`:

```simple
fn main():
    val b = (255 & 0xFF).to_u8()
    print("CHK to_u8_ok")
    var parts: [text] = ["a", "b"]
    print("CHK join=" + parts.join(","))
    print("CHK done=1")
```

| lane | result |
|------|--------|
| `SIMPLE_EXECUTION_MODE=interpret` | `CHK to_u8_ok` / `CHK join=a,b` / `CHK done=1` |
| `bin/simple native-build <entry>` | `RC=1`, no binary, both methods unresolved |

The probe deliberately imports nothing, to prove the gap is general rather than an
artifact of a particular module or of a larger probe.

## Why this matters — it blocks verification of landed security fixes

Both methods are load-bearing in code that landed 2026-08-07/08 carrying an
"interpreter-only" caveat, so that caveat **cannot currently be discharged natively**:

- **`to_u8`** — `src/lib/common/aes/modes.spl:31` (`_i64_to_u8`, the `[i64]`→`[u8]`
  bridge that *every* `aes_cbc_encrypt` / `aes_cbc_decrypt` / `aes_ctr_*` entry point
  calls, at lines 60/74/167/189/214/231) and **28 occurrences** in
  `src/lib/common/crypto/aes_gcm.spl`. The entire typed AES path is unbuildable
  natively. This is the direct blocker on the native half of
  `credential_store_aes_cbc_label_is_actually_ctr_with_deterministic_iv_2026-08-07.md`
  (fix `23839a41331`).
- **`join`** — `src/lib/nogc_sync_mut/database/sql/escape.spl:20,33,122`, i.e.
  `quote_ident` and its siblings, which are exactly the identifier-quoting path added by
  the SQL savepoint injection fix `021f5171208`.

So two landed security fixes are verifiable on the interpreter and the seed JIT, and
**not verifiable at all** on the pure-Simple native lane until these lowerings exist.

## What this is NOT

Not a native-build outage. `native-build` is working: a sibling probe
(`.nvprobe/scope_id.spl`) built and ran successfully (`RC=0`, 30 KB binary) in the same
window under load ~60–92. The earlier "total native-build outage" report was already
refuted by `a9c8effc054`; this is two specific missing method lowerings, nothing wider.

## Note on diagnostics

The failing log still contains `[stderr truncated by native-build entry]` even after
`a9c8effc054`. The load-bearing `error:` lines survived in this instance, but the marker
means a truncation path is still live — do not trust a `grep -c` over native-build
stderr to be exhaustive; read the preserved-diagnostics region.
