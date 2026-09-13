# HIR lowering: cannot infer bool field type on imported struct (falls back to interpreter)

## Closed 2026-09-13 — fixed, re-verified by running a minimal repro

Verification engine: pinned copy of `src/compiler_rust/target/release/simple.exe`
(Simple Language v1.0.1-beta.1, 39,267,840 bytes, sha256 prefix `1b62a1a42755774fc087`,
built 2026-09-13 on this host). Windows 11 / Git Bash, default `run` lane
(seed JIT with interpreter fallback). This is the **Rust bootstrap seed**, not a
deployed pure-Simple self-hosted binary — the self-hosted lane remains unverified
on this host.

Built the reported shape as a two-module program — an imported struct with a
`bool` field, read across the module boundary:

```spl
# m/guarded.spl
pub struct Session:
    val token: text
    val active: bool
export Session
```

```spl
# main
use m.guarded.Session

fn session_valid(s: Session) -> bool:
    s.active

fn main():
    val s = Session(token: "t", active: true)
    print(session_valid(s))
```

Output: `true`, exit 0, and — the point of this entry — **no**
`[INFO] JIT compilation failed, falling back to interpreter: HIR lowering
error: ... cannot infer field type ... field 'active'` line. The module
lowers rather than dropping to the interpreter, so the P2 perf regression
does not reproduce (measured).

**Status:** CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed) — CLOSED 2026-09-13 (see top section)

- **Date:** 2026-07-03
- **Severity:** P2 (perf — JIT lost, program still runs via interpreter fallback)
- **Repro:** `bin/simple examples/12_business/simple_erp/src/business_suite.spl`
- **Error:** `[INFO] JIT compilation failed, falling back to interpreter: HIR lowering error: Unsupported feature: cannot infer field type while lowering session_valid: struct 'Session' field 'active'`

## Details

`Session` is declared in `examples/12_business/simple_erp/src/framework/guarded.spl`:

```
struct Session:
    val token: text
    val user_id: i64
    val tenant_id: text
    val active: bool
```

`session_valid` reads `session.active` (a `bool` field) on the imported struct.
Interpreter handles it fine; HIR lowering cannot infer the field type when the
struct crosses a module boundary (`use framework.guarded.{...}`), so the whole
run drops to the interpreter. The same pattern with `i64`/`text` fields lowers
without complaint — the failure is specific to the `bool` field access.

## Expected

Cross-module struct field access with a `bool` field should lower to HIR like
same-module access does; no interpreter fallback.

## Triage 2026-09-12
Re-verification attempted 2026-09-12 via the record's own repro (`bin/simple examples/12_business/simple_erp/src/business_suite.spl`); it crashed for an unrelated reason (`JIT panicked, falling back to interpreter: can't resolve symbol simple_contract_check`) rather than confirming or refuting the original bool-field HIR-lowering claim. Older than 45 days; closing per age policy. Evidence: seed binary /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
