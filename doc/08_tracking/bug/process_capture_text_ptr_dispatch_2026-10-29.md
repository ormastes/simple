# Seed-produced process capture leaves text.ptr unresolved

Status: process-capture call site repaired with a monomorphic text ABI bridge;
general compact `.ptr()` dispatch gap remains open.

Fresh combined Stage 2 candidate SHA256
`497875533960b61150c4f493aacd5e1cb4d0a9078b0b752e215b12a2e0529483`
failed strict frontend sanity before SCV inventory: `Function 'str.ptr' not found`
(exit 70). LLDB stopped in `rt_function_not_found`, called from
`process_capture_unbounded_native+100`, then process operations,
`workaround_git`, `refresh_workarounds`, and the native-build worker.
Evidence: `/tmp/simple-phase2-lldb18/rejected-str-ptr.log` and
`/tmp/simple-release-1.0.0-phase2-combined-build-20261029/stage3/aarch64-unknown-linux-gnu/stage2-sanity.env.frontend-failure.log`.

Commit `b022993ee86` changed command extraction from a generic extern to
`retained_command.ptr()`. The seed-produced candidate left that method as
dynamic `str.ptr`; the pure-Simple MIR has a dedicated lowering, so one producer's
native success did not establish bootstrap producer parity. This is unrelated
to the parser claim-window and allocation-free suffix repairs.

The scoped repair keeps returned runtime handles on the existing monomorphic
i64 ABI and borrows command bytes through a separate monomorphic
`rt_string_data(value: text)` declaration. No generic/Any extern is restored.
The caller retains the text through the synchronous process-provider call.
The established text accessor in `sffi/codegen.spl` uses the same runtime ABI.

## Executed parity evidence

The Linux native probe under `test/01_unit/compiler/driver/` checks all eleven
UTF-8 bytes of literal and owned `A한글🙂`, bounded stdout/stderr and exit 7,
and unbounded stdout, the existing empty-stderr result and exit 7. Both native
artifacts ran once and printed `PASS process-capture-text-bridge UTF8 bounded
unbounded status7`, exit 0. Producer/source/runtime/tool hashes were recorded
and checked unchanged during each build.

| Producer | Evidence directory | Artifact SHA256 | Build peak KiB |
|---|---|---|---:|
| retained pure-Simple `e3a7e65cdad2aea37939056f5f115053733e342a89f0507eaec3ede9212233d6` | `/tmp/simple-process-capture-pure-probe3-20261029` | `27d53e987ffbd2ba68f3c3e455ead4430507161be735a01aa6534a6ca5fae3ff` | 2683996 |
| exact Rust bootstrap producer `f4af78b7f903d564cd1980cb4d171451a65d3ef4a31292ca06e7b6275c7358ef` | `/tmp/simple-process-capture-seed-probe2-20261029` | `fa197f1fc31fb9675d094e2c01a83db14960e4fe9f5a29cbc7f20d8bb7f481f0` | 235968 |

The Rust run is an isolated bootstrap-producer regression, not a fallback
for general testing. The rejected Stage 2 candidate was not used as producer.
Guide and Astra reviewed the bridge with no P0/P1/P2 findings.

## Separate failures and limits retained

- Initial `test/fixtures/native_process_capture_word_abi/main.spl` compile was
  rejected by parse-shard source admission (zero collected sources). Its
  enhanced portable fixture was not qualified; the admitted test/01_unit probe
  supplies the executed evidence. Log: `/tmp/simple-process-capture-pure-probe-20261029/probe.log`.
- The first pure probe inferred its expected numeric array and failed the
  UTF-8 comparison. LLDB verified length 11, a nonzero pointer and the exact
  bytes. Adding the existing fixture's explicit `[i64]` annotation made the
  otherwise unchanged byte oracle pass. The inferred-array code-generation
  discrepancy remains open; evidence: `/tmp/simple-process-capture-pure-probe2-20261029`
  and `/tmp/simple-phase2-lldb18/bridge-values.log`.
- The existing C unbounded provider redirects stderr but unconditionally
  returns an empty string (`rt_process_run_array`). The first seed probe
  exposed this with exact stdout/exit 7 and empty stderr; it is not a bridge
  corruption or evidence of stderr capture. Bounded stderr transport passed.
- SFFI backlog audit remains failed on existing inventory totals
  (`source_variants=409/399`, `migration=3736/3546`).
- No claim of general `.ptr()` repair, full compiler/core/MCP verification or
  bootstrap admission is made. A fresh combined Stage 2 sanity remains required.
