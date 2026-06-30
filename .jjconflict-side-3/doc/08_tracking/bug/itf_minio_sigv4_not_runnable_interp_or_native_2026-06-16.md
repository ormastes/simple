# itf minio SigV4 HTTP round-trip not runnable (interpreter or naive native compile)

- **ID:** itf_minio_sigv4_not_runnable_interp_or_native_2026-06-16
- **Severity:** P2
- **Area:** app/itf (minio), runtime HTTP extern, interpreter/native compile
- **Date:** 2026-06-16
- **Status:** Partially resolved (interpreter `rt_http_request` now works; JIT bridge + module/native gaps remain)

## Summary

`bin/itf minio {health,ls,...}` dispatches correctly and loads config. The
`rt_http_request` extern is now registered in the interpreter and performs a
**real HTTP round-trip under interpret mode** (verified live against a local
MinIO: status `403` + 254-byte XML body, read correctly via both tuple field
access and destructuring). The remaining gaps are below.

## Resolved

- **`rt_http_request` interpreter registration** — registered in the bootstrap
  interpreter extern table (`insert_simple!("rt_http_request", network::rt_http_request)`)
  with a real `ureq`-backed impl mirroring `rt_http_get`. Verified live:
  `SIMPLE_EXECUTION_MODE=interpret simple_seed run` against `http://127.0.0.1:9000/`
  returns `(403, <254B XML>, "")`, destructured correctly by the adapter idiom
  `val (status, body, err) = rt_http_request(...)`. The prior
  `E1002 unknown extern function: rt_http_request` is gone.

## Remaining blockers

1. **JIT-mode tuple-return bridge (default run mode)** — under the default JIT
   execution mode, externs that return a tuple bridge back through
   `interp_call_handler` (`interpreter_sffi.rs`) → `value_to_runtime`
   (`runtime_bridge.rs`) → compiled code, and the **compiled consumer reads the
   tuple as garbage** (`.0` → 0, `.1` → invalid pointer). This is **pre-existing
   and family-wide**: the shipped `rt_http_get` fails identically in JIT mode.
   So today the HTTP externs only work via `SIMPLE_EXECUTION_MODE=interpret`.
   Filed/observed here; a focused fix belongs in the JIT tuple round-trip, not
   the minio adapter.
2. **`http_client.types` module resolution** — `bin/itf minio` (default JIT)
   still surfaces `Export statement references undefined symbol name=rt_http_request`
   (a non-fatal WARN under interpret mode) and the
   `nogc_sync_mut.http_client.types` chain does not resolve in some import forms.
   Same family as [[interp_http_url_encode_utilities_unresolved_2026-06-14]].
3. **Naive native compile** — `bin/simple compile src/app/itf/main.spl` fails
   with `semantic: Undefined("undefined identifier: platform")`, a separate
   compile-path module/global gap. There is no `itf` build target/prebuilt
   binary in the repo.

## Reproduction

```bash
export SIMPLE_BOOTSTRAP_DRIVER=bin/release/x86_64-unknown-linux-gnu/simple_seed
SEED=bin/release/x86_64-unknown-linux-gnu/simple_seed

# rt_http_request now round-trips under interpret mode (live MinIO on :9000):
cat > /tmp/probe.spl <<'SPL'
use std.nogc_sync_mut.io.http_sffi.{rt_http_request}
fn main() -> i64:
    val (status, body, err) = rt_http_request("GET", "http://127.0.0.1:9000/", [], "")
    print "STATUS:{status} BODYLEN:{body.len()} ERR:{err}"
    0
SPL
SIMPLE_EXECUTION_MODE=interpret "$SEED" run /tmp/probe.spl
#   STATUS:403 BODYLEN:254 ERR:

# Default JIT mode still garbles the tuple (pre-existing, also affects rt_http_get):
"$SEED" run /tmp/probe.spl
#   STATUS:0 BODYLEN:-1   (raw RuntimeValue tuple leaks into compiled consumer)

# Native compile still fails before producing an artifact:
bin/simple compile src/app/itf/main.spl -o /tmp/itf
#   error: compile failed: semantic: Undefined("undefined identifier: platform")
```

## Evidence the server/creds are NOT the cause

A local `minio/minio:latest` container (throwaway creds) was confirmed fully
functional via `mc`: alias set, `mc mb`, `mc cp`, and `mc ls --recursive` all
round-tripped (object `firmware-images/zynq/v1/fw.txt`, 26B). Only the Simple
binary path failed. (Container + creds + mc alias were torn down after the run.)

## Impact

- The minio adapter (`adapter_minio.spl`, pure-Simple SigV4) is now
  behavior-verifiable end-to-end **under interpret mode**; the default JIT run
  mode is blocked by the pre-existing tuple-bridge bug above.
- Same JIT/module blockers affect any itf command that makes real in-Simple HTTP
  calls (jira/confluence/bitbucket/outlook curl adapters shell out instead, so
  those are unaffected; minio is REST-in-Simple, so it is affected).

## Fix options (hypotheses — verify against runtime)

1. **(DONE)** Register `rt_http_request` in the interpreter extern table so REST
   adapters run under the seed driver in interpret mode.
2. Fix the JIT tuple-return bridge so compiled consumers read tuples returned by
   `interp_call_handler` correctly (would also fix the shipped `rt_http_get`).
3. Resolve the `nogc_sync_mut.http_client.types` module chain in all import forms.
4. Provide an `itf` native build target that resolves `platform`, enabling an
   AOT binary that links the runtime HTTP extern.
