# BUG: text.len() miscompiled by LLVM native backend (returns -1 on rv64 freestanding, 0 on host)

**Status:** open — sole blocker for the SimpleOS rv64 DB-server gate going green
**Severity:** high (silent wrong values from a core primitive; drops last byte of every sliced body)
**Component:** LLVM native backend — text method lowering (`.len()` on `text`)
**Found:** 2026-07-11 (rv64 DB-gate lane, root-caused with minimal repro + padded-body counter-probe)

## Symptom

`request.len()` in freestanding rv64 LLVM-native code returns **-1** (host native: **0**; interpreter: correct). Downstream in `src/os/services/database/simple_db_service.spl`:

- `request.slice(sep+4, request.len())` → `slice(sep+4, -1)` → `rt_slice` treats -1 as `len-1` → the body's **last byte is dropped**: `POST /db "CREATE codex"` stores table `"code"`; the later `INSERT codex ...` then fails `ERR table not found` (gate: `FAIL db_success_response_count_missing`).
- Every HTTP response carries `Content-Length: -1`.

## Evidence chain

- Serial debug: stored table `t0=[code]`; `CREATE codex` → `CREATE codey` wrongly reports "table exists" (both truncate to "code").
- Minimal host repro (`len_repro.spl`): native `direct_len=0` vs interpreter `5` for the same `text.len()` call.
- Counter-probe: padding each command body with a trailing space makes the FULL gate section pass (`DB CREATE/INSERT/SELECT... PASS (codex-41)`), proving parsing, state persistence, class mutation, and the TCP path are all correct — only `.len()` is wrong.
- Source-level hoisting (`val body_len = body.len()`) does NOT fix it — the call itself returns the wrong value. An earlier hoist workaround with a wrong root-cause comment ("chained-method bug") was reverted; this is not the chained-method issue (89ab4ff3 landed; this reproduces without chaining).

## Where

The rv64 DB server itself is real and live: in-memory `SimpleDbService` (`src/os/services/database/simple_db_service.spl`) wired into the boot HTTP loop (`src/os/kernel/boot/http_baremetal.spl`); gate `scripts/qemu/qemu_rv64_http_test.shs --expect-http-only --with-db` + checker `scripts/qemu/check_simpleos_rv64_db_server.shs`. HTTP-only section passes 4/4; only the DB section fails, entirely via this bug.

## Fix direction

LLVM backend text-method lowering: `.len()` on `text` must lower to the runtime length read (as the interpreter does), not whatever produces 0/-1. Regression: compile `val s = "hello"  print("{s.len()}")` LLVM-native on host and rv64-freestanding; expect 5.
