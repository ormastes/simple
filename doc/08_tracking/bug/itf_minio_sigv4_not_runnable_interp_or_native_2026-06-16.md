# itf minio SigV4 HTTP round-trip not runnable (interpreter or naive native compile)

- **ID:** itf_minio_sigv4_not_runnable_interp_or_native_2026-06-16
- **Severity:** P2
- **Area:** app/itf (minio), runtime HTTP extern, interpreter/native compile
- **Date:** 2026-06-16
- **Status:** Open

## Summary

`bin/itf minio {health,ls,...}` dispatches correctly and loads config, but the
actual S3 SigV4 HTTP request cannot execute in either run mode available in this
repo:

1. **Interpreter (seed driver)** — the HTTP path fails with
   `error: semantic: variable `types` not found`, preceded by
   `Export statement references undefined symbol name=rt_http_request`. The
   `rt_http_request` extern is not registered in the interpreter, and the
   `nogc_sync_mut.http_client.types` module chain does not resolve. Same family
   as [[interp_http_url_encode_utilities_unresolved_2026-06-14]] (the
   `http.common`/`utilities` resolution gap).
2. **Naive native compile** — `bin/simple compile src/app/itf/main.spl` fails
   earlier with `semantic: Undefined("undefined identifier: platform")`, a
   separate compile-path module/global gap. There is no `itf` build target,
   recipe, or prebuilt binary in the repo.

Net effect: the minio adapter's success path (any real network call) cannot be
verified by running the Simple binary in this environment. Dispatch, config
loading (`auth.sdn` `[minio]`), and both auth-error paths DO run and were
verified.

## Reproduction

```bash
export SIMPLE_BOOTSTRAP_DRIVER=bin/release/x86_64-unknown-linux-gnu/simple_seed

# Interpreter: dispatch + auth errors work...
bin/simple run src/app/itf/main.spl minio health   # error: MinIO URL not configured (no creds)
bin/simple run src/app/itf/main.spl minio ls        # error: MinIO auth not configured. Set [minio]...

# ...but with a real [minio] section in ~/.config/itf/auth.sdn pointed at a live
# MinIO (verified reachable via `mc`), the HTTP call fails:
bin/simple run src/app/itf/main.spl minio health
#   WARN Export statement references undefined symbol name=rt_http_request
#   error: semantic: variable `types` not found

# Native compile fails before producing an artifact:
bin/simple compile src/app/itf/main.spl -o /tmp/itf
#   error: compile failed: semantic: Undefined("undefined identifier: platform")
```

## Evidence the server/creds are NOT the cause

A local `minio/minio:latest` container (throwaway creds) was confirmed fully
functional via `mc`: alias set, `mc mb`, `mc cp`, and `mc ls --recursive` all
round-tripped (object `firmware-images/zynq/v1/fw.txt`, 26B). Only the Simple
binary path failed. (Container + creds + mc alias were torn down after the run.)

## Impact

- The minio adapter (`adapter_minio.spl`, pure-Simple SigV4) can be reviewed and
  signature-verified but not behavior-verified against a live endpoint from this
  repo until either (a) the interpreter registers `rt_http_request` + resolves
  the `http_client.types` chain, or (b) a working native/AOT build of `itf`
  exists (resolve the `platform` identifier).
- Same blocker family affects any itf command that makes real HTTP calls
  (jira/confluence/bitbucket/outlook curl adapters shell out instead, so those
  are unaffected; minio is REST-in-Simple, so it is affected).

## Fix options (hypotheses — verify against runtime)

1. Register `rt_http_request` (and the `http_client.types` module) in the
   interpreter extern/module tables so REST adapters run under the seed driver.
2. Provide an `itf` native build target that resolves `platform`, enabling an
   AOT binary that links the runtime HTTP extern.
3. As an interim, expose the minio adapter behind the same subprocess/curl
   pattern the other adapters use, so it is runnable without the in-Simple HTTP
   stack.
