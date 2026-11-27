# Stage 2 CLI build exceeds 60 GiB RSS cap (1551-module leak_check closure)

- **Status:** open
- **Found:** 2026-11-27, bootstrap of pinned `967f9178950e` (release/1.0.0 head)
- **Evidence:** Rust seed-built Stage 2, bootstrap verification campaign. Diagnostic only.

## Symptom
`stage2-compiler-tests` ABORTED during `compiler_cli_build` after about 3.5 h:
`primary_status=rss-cap-exceeded`, `rss_limit_kib=62914560`
(in `logs/aarch64-unknown-linux-gnu/stage2-compiler-tests.log`).
The tree RSS went from 55 GB to 62 GB in the last 60 s. The last progress line was
`phase=hir ... done=1119 total=4204 succeeded=513 cached=606 failed=0`. There were no error lines.

## Cause (diagnosed from logs; not reproduced)
- **Two workers live together.** Both file workers stayed alive for the whole run, at 18–29 GB RSS each.
  In the earlier pin `3dd00937c329`, owner 1 died on
  `FILE-WORKER-E-CLOSURE-INCOMPLETE` (fixed by #12126), so that run used one worker from there on and
  never reached this point.
- **One unusually large unit.** Owner 1 picked a unit with a
  `mir-child hir closure modules=1551 of=7187` (log line 639742); every other
  unit across four pins tops out at 432–549 modules. The unit covers `app/devhub/*`,
  `compiler/90.tools/leak_check/*` and `mem_tracker`. It lowered 513 modules fresh; normal units lower 1–16.
- **The import behind it.** `src/compiler/90.tools/leak_check/external_runner.spl:9` has a plain
  `use compiler.driver.driver_api_codegen_backends.{aot_c_file}`, which pulls in most of the
  driver for one function. Only 12 of the 1189 lowered modules are braced re-export facades, so
  #12126 did not enlarge the closure. The import is the same at `3dd00937c329`.
- **Breach mechanism.** Two workers at about 27 GB, plus a new MIR child started by owner 0 in the final 29 s,
  together exceeded the 60 GiB tree cap. This is an inference: the `rss.env` files hold only tree totals.

## Workaround
Run the verification with one module worker:
`BOOTSTRAP_VERIFY_MODULE_WORKERS=1` (default 2, `scripts/bootstrap/bootstrap-phase-verification.shs:224`).

## Fix options (owner)
1. Narrow `leak_check/external_runner.spl` so it does not import `driver_api_codegen_backends`
   for `aot_c_file`, for example by moving the helper to a leaf module.
2. Have the file-worker planner bound or split a unit whose HIR closure is more than about 2× the usual maximum.
