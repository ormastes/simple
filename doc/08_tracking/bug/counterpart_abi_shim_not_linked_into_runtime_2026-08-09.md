# Counterpart ABI shim is not linked into the runtime — `rt_counterpart_*` unresolved

Date: 2026-08-09
Status: OPEN — blocks the Wave-1 F1 exit gate
Severity: high for the counterpart lane; no impact outside it.

## Symptom

`test/01_unit/infra/counterpart/counterpart_abi_spec.spl`:

```
declared>=8 executed=8 passed=1 failed=7   rc=1
semantic: unknown extern function: rt_counterpart_open
```

The module parses and loads — the one pure-Simple example passes — so this is
not a syntax or import fault. The seven failures are all the same cause: the
externs declared by `src/lib/nogc_sync_mut/sffi/counterpart_abi.spl` have no
symbol behind them because `src/runtime/counterpart_abi_runtime.c` is not
compiled into the runtime the binary under test links.

## What IS proven

The C layer works. Measured through a temporary C driver (since deleted):

| Probe | Result |
|---|---|
| `probe_abi(1)` / `probe_abi(2)` | `1` / `0` — version negotiation refuses v2 |
| bogus library path | `-2` |
| `open` | handle `1` |
| manifest | 1640 bytes, all four components present |
| `mock.echo` round-trip | byte-correct including escaping |
| `mock.hash("abc")` | `e16801510db89efd`, identical across two invokes |
| `mock.error` | status 0 with `status: error`, `error_code: mock.deliberate_failure` |
| unknown component | `2` |
| `reset` / `close` / `close` again / `reset(999)` | `0` / `0` / `-9` / `-9` |
| `mock.crash` child | exit `134` (SIGABRT) — crash is observable, not swallowed |

Both C files compile clean under `cc -c -std=c99 -Wall -Wextra`. The mock adapter
builds to `build/counterparts/libsimple_counterpart_mock.so`.

## Why it was not fixed in the lane

Making `rt_counterpart_*` resolvable requires editing three shared compiler
files — `src/compiler/70.backend/backend/runtime_compiler.spl` (runtime source
and object lists), `llvm_native_link.spl` (candidate labels) and
`stage4_symbol_closure.spl` — and then rebuilding the runtime and re-deploying
the binary. Those files are outside the F1 path set and are shared with other
concurrently-running lanes, and the edit is not verifiable without a full
runtime + bootstrap rebuild. Landing an unverifiable edit to shared codegen
files was judged worse than reporting the blocker.

Note that the lists above govern the **native-build** lane. `bin/simple run`
resolves externs from the runtime linked into the deployed binary, so a runtime
rebuild alone is not sufficient — the binary must be rebuilt and redeployed too.

## Unblock condition

1. Add `counterpart_abi_runtime` to the runtime source/object lists in
   `runtime_compiler.spl`, the link candidate labels in `llvm_native_link.spl`,
   and the stage-4 symbol closure.
2. Rebuild the runtime and re-deploy the self-hosted binary
   (`scripts/setup/setup.shs && bin/simple build bootstrap`, then re-copy to the
   launch path).
3. Re-run `bin/simple run test/01_unit/infra/counterpart/counterpart_abi_spec.spl`
   and require 8 examples / 0 failures.
4. Then sabotage-probe: corrupt the adapter's reported `abi_version` and confirm
   the spec goes RED rather than silently accepting the library.

Until step 3 passes, the F1 exit gate ("load, manifest, open, invoke, reset,
close from Simple") is NOT met, and no guide may claim the counterpart ABI is
reachable from Simple code.

## Related

- `tools/counterpart/sdk/c/simple_counterpart_abi.h`
- `tools/counterpart/adapters/mock/simple_counterpart_mock.c`
- `src/runtime/counterpart_abi_runtime.c`
- `src/lib/nogc_sync_mut/sffi/counterpart_abi.spl`
- Plan: `doc/03_plan/infra/counterpart/counterpart_conformance_parallel_agent_plan_2026-08-09.md` (Wave 1, F1)
