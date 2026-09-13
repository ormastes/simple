# Site 11: the Stage-2 route now REACHES llc and emits invalid IR (duplicate local name)

- **Status:** OPEN (2026-09-13)
- **Lane:** BOOT-9, found on `build/bootstrap-boot9b` (09:43:56 -> 09:52:48,
  head `c541c610d86`, `--full-bootstrap --backend=llvm --mode=dynload --jobs=10
  --stop-after-stage2`)
- **Severity:** the current `--stop-after-stage2` admission blocker, successor to
  sites 9 (`stage2_stage3_route_native_compile_timeout_2026-09-13.md`) and 10
  (`stage2_unwrap_on_array_pop_yields_nil_2026-09-13.md`), both fixed.
- **Candidate:** `build/bootstrap-boot9b/stage2/aarch64-unknown-linux-gnu/simple`,
  sha256 `99ba0cf430d255a4141edfc7...`, 152198144 B (pin
  `scratchpad/boot9/pin/cand.boot9b.stage2`).

## The failure kind CHANGED, which is the progress

Sites 9 and 10 both showed as `status 124` — the route was killed by the gate's
180 s ceiling while allocating without bound. It now fails as `status 1` with a
concrete diagnostic, in seconds:

```
| error: stage2 failed the positional pure-Simple Stage-3 route (status 1)
| /usr/lib/llvm-18/bin/llc: error: .../simple-llvm-aot-*/module.ll:102:3:
  error: multiple definition of local value named 'l13'
error: in-process native-build: build failed: 2 failed, 0 unverified, 0 not run,
  0 ok of 2 unit(s) — ERROR:
  scripts.check.cert.redeploy_gate.fixtures.stage2_module_path_naming,
  compiler.common.module_path_naming
```

Both units fail the same way. Reproduced standalone in seconds with the gate's
own env and fixture (`scratchpad/boot9/route11.log`, `route11b.log`).

## One variable: which compiler emits the IR

| compiler emitting the IR | result |
|---|---|
| the bootstrap's LLVM-capable **Rust seed**, `--backend llvm`, same fixture, same runtime authority, same flags | **PASS** — `1 compiled, 0 failed`, and the produced binary prints exactly the fixture's EXPECT block: `app.cli.bootstrap_main` / `compiler.driver.driver` / `app.cli.main` (`scratchpad/boot9/seed_fixture_build.log`) |
| the **Stage-2 candidate** (pure-Simple emitter) | FAIL — `multiple definition of local value named 'l13'` |

So the defect is in the pure-Simple LLVM text emitter's local-value naming, not
in the fixture, the MIR, the runtime, llc, or LLVM 18. Locals are named `l<N>`
from MIR local ids (`src/compiler/70.backend/backend/_MirToLlvm/`), so a
duplicate `l13` means one MIR local id is DEFINED twice inside one function
body without renaming — LLVM text IR requires each local value name to be
defined exactly once per function.

## Next step for whoever picks this up

The `.ll` is deleted even with `SIMPLE_BOOTSTRAP=1` and
`SIMPLE_KEEP_LLVM_IR=1` (the guard at
`src/compiler/70.backend/backend/llvm_backend_tools.spl:242-243` skips ITS
cleanup in that case, so something else removes the stage dir — probably
`rt_secure_temp_dir`'s own teardown). Making that retention actually work is the
first step; without the IR, line 102 cannot be attributed to a MIR instruction.
A cheap alternative is to emit the module to a caller-chosen path.

Do NOT raise `STAGE2_SELFHOST_ROUTE_TIMEOUT_SECONDS`: it is no longer even
involved — the route fails fast now.
