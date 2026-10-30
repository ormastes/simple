# Small-module Phase2 execution proposal — 2026-10-26

**PLANNED / NOT_RUN.** This document authorizes nothing by itself. Root must
review the frozen inputs and separately authorize execution. Inspection base:
`3006afa9b4dd286e3beb304dbe4f1a57cf5d87a8`, shared worktree
`D:/dev/simple-coremux-shared-20261025`. No compiler, build, test or native
process ran during this planning lane; no production files were edited.

## What the existing implementation supports

`std.common.test_runner.native_framework_wrapper.native_framework_wrapper_source`
is the canonical pure native wrapper owner. The production executor calls it
with the original source and the actual compiler lexical facts:
`simple_code_lines`, `simple_string_continuation_lines` and
`simple_string_byte_ranges` from `compiler.frontend.core.source_facts`.
It preserves generic `std.spec` imports, real describe/context/it/hook closures,
declarations and matchers. Its generated main calls framework `print_summary`,
returns 2 for zero executed cases, otherwise returns framework `get_exit_code`.
It creates no replacement matcher or verdict engine.

Use that owner through a small reviewed Simple generation driver, then compile
and execute the generated real-framework programs. This is actual native SSpec
execution if the controls succeed; it is not validation of the full test CLI,
its discovery/cache/cleanup pipeline, or explicit configured-memory selection.
Do not use the legacy SMF branch: it substitutes inline helpers and removes
framework imports. Do not equate a native assertion probe with SSpec execution.

The immutable compiler supports `native-build`; its `--library-mode` rejection
is already recorded in `doc/09_report/smux_phase2_configured_build_attempt_2026_10_26.md`.
Use **library_mode: unset; effective_profile: legacy-unset/unverified** for this
interim cohort. Generic imports stay generic. Do not spoof internal worker flags,
infer profile from module directories, or rewrite `std.spec` to force a family.
Record actual resolved framework paths from dependency/build receipts when
available; absence of those paths is missing profile evidence, not NoGC proof.

## Historical attempts are retained

The retained real-runner attempt at
`C:/dev/simple-test-runner-direct-20261025/evidence/terminal.sdn` is FAILED,
exit 1, candidate absent, real SSpec examples executed 0. Its
`compile/runner.log` reports unresolved
`app.test_runner_new.test_runner_main` from a private entry-only project.
Its inputs identify source `b66b7b1f78562719ea803d7558300c3d2f054eb0`, the
same immutable compiler, 24 jobs and monitor-only RSS. Preserve that receipt;
do not reuse its resource policy or call its source layout a successful route.

Bounded follow-up located the additional runner:
`D:/dev/simple-devhub-release-20261025/build/devhub-system/simple_test_runner.exe`,
SHA-256 `7c6813f09294759dca353bdea76936f6c5a5d85ae210a088b4204573633883bf`.
Its source report is that worktree's
`doc/09_report/verification/devhub_release_system_tests_20261025.md`;
`build/devhub-system/wall-clock-sspec-native.log` retains the failed file verdict.
The report records owned-process admission failure before compilation, an
earlier TMPDIR/TEMP issue, an unavailable scoped-environment output route, and
a separate legacy-generated-entry unresolved-import compile failure. File
verdict counts in that old log are not actual SSpec-body execution counts.
Preserve these historical failures and their original diagnostics. Root
must carry the unknown cumulative count visibly in the execution ledger and
reconcile it before claiming retry-budget availability; no reset is authorized.
A fresh driver/output directory does not reset the six-cycle harness cap. The cache-generator
diagnostic series is separately exhausted; neither this driver nor the feature
cohort authorizes any cache-generator retry. New module verification rows retain
their own actual prior fix/verification counts. No automatic retries.

During preparation root reported one new H0 supervisor-script UTF8-BOM setup
failure before compiler launch; preserve it separately as setup failure with
zero SSpec cases. The frontend was then deferred because another session's
full-objects P2 build was active: root PID 58224 and worker PID 996, with the
worker observed at approximately 20506 MiB. This is a retained observation
reported by root, not a current process-status claim or a measurement from
this planning lane. No compiler
invocation or harness pass follows from preparing this plan/driver.

## Minimal fixture-generation method

Root authorized source preparation of the concrete driver
`test/fixtures/test_runner/native_framework/generate_controls.spl`, SHA-256
`61a6cdbd347955f369d7e31ef46ea0789546f9e0200a709829ac5b6daeb2da35`.
This durable fixture is an exact byte copy of the private preparation artifact
`build/review/smux-small-module-phase2-wrapper-driver.spl`; output paths are
unchanged. It has been authored, not compiled or run. It imports only the canonical wrapper, the three lexical
fact functions and existing `app.io.file_ops.{file_read, file_write}`. A fixed,
reviewed manifest supplies original spec path and distinct output path pairs;
no directory discovery, test filtering or dynamic fallback is needed.

For each pair, the driver reads the original spec, rejects empty/unreadable
content, calls the canonical wrapper with all three actual lexical fact arrays,
propagates wrapper errors, and writes the resulting source only after success.
Write failure is nonzero. Existing reviewed outputs must not be overwritten.
Root hashes input, driver and output and independently checks preservation of
the real framework calls and generated zero-case guard. No host-language
reimplementation of partitioning or lexer masks, regex rewrite, replacement
`expect`/`it`, or fabricated counter is allowed. Driver success counts as
generation only, with **SSpec cases executed: 0**.

The concrete driver uses both existing fixture paths below and writes to
`build/review/smux-small-module-phase2-generated/hooks_and_siblings_native.spl`
and `build/review/smux-small-module-phase2-generated/failure_continuation_native.spl`.
Root must create that empty output directory before its first authorized run.
Both paths are fixed, and existing outputs are refused. If the second write
fails, preserve the first partial artifact and report generation failure; do not
silently overwrite/retry it. Only after both controls pass,
extend the finite manifest with each independently frozen small-module spec.
The driver must retain the original source-module imports; `--source src`
provides the actual library/compiler/app closure and avoids the historical
entry-only project import failure. Generated declarations retain module scope.

## Producer, runtime and tool inputs

Use these existing paths, rehash before admitted launch and fail on drift:

| Input | Path / retained SHA-256 |
|---|---|
| Compiler | `C:/dev/simple-disk-headroom-warm-bootstrap-storage-20261025/output/stage3/simple.exe`; `13d73267e690b2cdd46438315e2bfe6d4d6c0c37bcfc15591a921fc9728b270b` |
| Runtime directory | `C:/dev/simple-disk-headroom-warm-bootstrap-storage-20261025/runtime-derived` |
| Runtime archive | `libsimple_native_all.a`; `8de6b6efc7d1591d6cbb4c4543f26d72634654dded1327fe4e064d5f3782a78d` |
| Runtime DLL | `simple_runtime.dll`; `cd82ae845f31f9c084d12ede1639b17f264a1ded23895e0bcc0a16055c90a089` |
| Clang | `C:/dev/simple-gnu-continuation-toolcache-20261024/llvm-mingw-20260922-ucrt-x86_64/bin/clang.exe`; `20ba1856942744291a6aaaf9f2c94f6d0cd7cac5aa9557fce96471dc7ef25d6f` |
| Bounded collector | producer `runner/run-process-group-bounded-log-windows.py`; `17f0935e23cc3cf017ecde0d9769d7c4a5582be01d7ffecaa6fb8c441eac7305` |
| RSS watchdog | producer `runner/process-tree-rss-watchdog.pl`; `1fa06c06b35674c8e11bb9ee03208af50f49b3ff99b796ee88a3caa10d4e3154` |

These runtime/tool hashes are retained receipt inputs, not newly executed
qualification. Pin the actual selected runtime sources/objects/link command and
generated executable as well. Legacy bootstrap runtime settings do not certify
the requested NoGC profile. The source root is this shared checkout; freeze
each closure's bytes and detect concurrent drift before/after a row. Never fold
unrelated dirty changes into the candidate.

## Exact command templates, not executed

Run from the shared worktree. `$row` is a pre-created, exclusive absolute
directory for one named row. For H0 set `$entry` to
`test/fixtures/test_runner/native_framework/generate_controls.spl` and `$artifact` to
`$row/wrapper-driver.exe`; for H1/H2 use the generated source paths above and
`$row/hooks-and-siblings.exe` / `$row/failure-continuation.exe`. Pass argument arrays to
the existing supervisors; do not concatenate a shell command string.

```powershell
$producer = 'C:/dev/simple-disk-headroom-warm-bootstrap-storage-20261025'
$compiler = "$producer/output/stage3/simple.exe"
$runtime = "$producer/runtime-derived"
$mingw = 'C:/dev/simple-gnu-continuation-toolcache-20261024/llvm-mingw-20260922-ucrt-x86_64'
$compileArgs = @($compiler, 'native-build', '--source', 'src',
    '--entry-closure', '--entry', $entry, '--backend', 'cranelift',
    '--target', 'x86_64-pc-windows-gnu', '--threads', '1',
    '--runtime-path', $runtime, '--cache-dir', "$row/cache/native",
    '--low-memory', '--go-to-end', '--output', $artifact)
$boundedArgs = @("$producer/runner/run-process-group-bounded-log-windows.py",
    '--output-parent', $row, '--log-leaf', 'compile.log',
    '--receipt-leaf', 'compile.receipt', '--helper-sha256',
    '17f0935e23cc3cf017ecde0d9769d7c4a5582be01d7ffecaa6fb8c441eac7305',
    '--max-bytes', '1048576', '--timeout-seconds', '175',
    '--term-grace-seconds', '2', '--root-exit-policy', 'wait-job', '--') + $compileArgs
$supervisedArgs = @("$producer/runner/process-tree-rss-watchdog.pl",
    '--max-rss-kib=5859375', '--rss-cap-mode=enforce', '--compiler-jobs=1',
    '--timeout-seconds=180', "--receipt=$row/memory.env", '--',
    'C:/dev/tool/Python312/python.exe') + $boundedArgs
# After root authorization only:
# & 'C:/dev/tool/Git/usr/bin/perl.exe' @supervisedArgs
```

Use a child-specific environment, retaining its full nonsecret delta in SDN:
`SIMPLE_WINDOWS_ABI=gnu`, `SIMPLE_MINGW_ROOT=$mingw`,
`SIMPLE_CC=$mingw/bin/clang.exe`, `CC=$mingw/bin/clang.exe`,
`SIMPLE_BOOTSTRAP=1`, `SIMPLE_NATIVE_BUILD_RUST=0`,
`SIMPLE_PARSE_SHARDING=0`, `SIMPLE_HIR_SHARDING=0`,
`SIMPLE_MIR_SHARDING=0`, `SIMPLE_SCV_INVENTORY_COLD_INIT=1`,
`SIMPLE_LIB=<shared-worktree>/src`, `SIMPLE_BOOTSTRAP_STAGE3_REQUESTED_ROUTE=direct`.
Assign row-private `SIMPLE_CACHE_DIR`, `SIMPLE_HIR_CACHE_DIR`,
`SIMPLE_RT_OBJ_CACHE_DIR`, `SIMPLE_USER_STORAGE_ROOT`, and
`SIMPLE_WORKTREE_STORAGE_ROOT`; record their concrete paths. Prepend the pinned
MinGW `bin` and Git `usr/bin` to PATH. Remove inherited explicit library-mode
selectors; record their names and absence. No global environment mutation.

This matches the admitted native-build argument/environment surface retained
in `build/review/phase2-cache-generator-3/invocation.sdn`; it does not rerun or
qualify that generator. The additional generated entry remains a proposal
requiring actual compile evidence. Do not add unsupported `--library-mode`.

For driver/fixture execution, use the same watchdog/collector nesting, with
`run.log`, `run.receipt`, `run-memory.env`, a 65536-byte log cap, 20-second
collector deadline, 25-second watchdog deadline and two-second cleanup grace.
The inner command is only the exact newly hashed executable plus the driver's
reviewed arguments, if any. Include the pinned runtime directory in child PATH.
Preserve exit 1 from the intentional-negative fixture as its required verdict;
do not normalize it to zero in the receipt.

## Finite ordered rows and admission

| Row | Work | Required evidence |
|---|---|---|
| H0 | Build and run canonical-wrapper driver | Compile/run exit 0; wrapper hashes; zero SSpec claim |
| H1 | Build/run `test/fixtures/test_runner/native_framework/hooks_and_siblings_spec.spl` wrapper | Total 3, passed 3, failed 0, executed 3, exit 0; hook order, nested case and sibling assertions actually run |
| H2 | Build/run `test/fixtures/test_runner/native_framework/failure_continuation_spec.spl` wrapper | Total 3, passed 2, failed 1, executed 3, exit 1; genuine `7 != 8` failure; both later siblings and failed-case after hook verified |
| M1 | Frozen exact-target module/spec | Real framework counts equal its reviewed case inventory; no failures/skips/pending; exit 0 |
| M2 | Frozen event-journal module/spec | Same; actual journal transitions/assertions, not a native probe |
| M3 | Frozen metadata-query module/spec | Same; actual frozen DTO/production calls |

Root schedules only one heavy compiler tree. Stop at a failed control; do not
run feature rows behind a broken framework. For module failures, retain output,
report concrete failure and fix within the remaining ledger budget. Do not
repeat a green criterion. Requalification is justified only by changed relevant
inputs or a new concern, with its prior attempts retained.

Counters must come from the generated program's actual framework summary and
return path. `get_executed_test_count` is passed+failed, excluding skips/pending.
A compile exit, missing output, discovery list, zero cases, crash or process
timeout cannot satisfy either control. Require no log truncation obscuring the
verdict, child-exit receipts, completed tree measurement, and no live descendants.
Capture source/spec/wrapper/compiler/runtime/artifact hashes, source HEAD plus
dirty-closure pins, command/env, counts, native exit, stdout/stderr, peak RSS,
duration and cleanup state. Record NOT_RUN separately from failed and passed.

## Inspected source pins

| Path | SHA-256 |
|---|---|
| `src/lib/common/test_runner/native_framework_wrapper.spl` | `297e616084c811a1e21548603948523f3877573baaf5b472f1bb65f5ff22f481` |
| `src/compiler/10.frontend/core/source_facts.spl` | `cc9627163d91f344711ea9e0bf3e1947c55b52890021f1d7ea4e20a41676062f` |
| `test/fixtures/test_runner/native_framework/hooks_and_siblings_spec.spl` | `628793d87896faac6fd5ea79f534321d344726a72bd285ca874ed70653d1cd83` |
| `test/fixtures/test_runner/native_framework/failure_continuation_spec.spl` | `09709cdaefcbb400f7b581fcc8c5400d7862948a18358abe409585442707d6eb` |

The fixtures' existing Phase3 NOT_RUN annotations remain historical; receipts
must label any newly authorized execution as interim Phase2. Full CLI transport,
explicit library-mode control, actual system/native backend workflows, formal
model gates and Phase3 qualification remain separate requirements. A successful
small-module cohort alone does not authorize landing the unfinished PR.

## Final driver import/signature source review

No compile-surface mismatch was found in the tracked driver's three imports
and calls. `app.io.file_ops` re-exports the existing
`std.nogc_sync_mut.io.file_ops` owner: `file_exists(text) -> bool`,
`file_read(text) -> text`, and `file_write(text, text) -> bool` match the
driver's branches. This concrete infrastructure facade is not evidence for
the feature cohort's configured library profile. The text writer's return
is not an independent byte-integrity proof; retained output hashes and the
generated-source review remain required before compilation.

`compiler.frontend.core.source_facts` resolves to the established
`src/compiler/10.frontend/core/source_facts.spl` module and explicitly exports
`simple_code_lines(text) -> [text]`,
`simple_string_continuation_lines(text) -> [bool]`, and
`simple_string_byte_ranges(text) -> [[i64]]`. The canonical wrapper explicitly
exports `native_framework_wrapper_source(text, [text], [bool], [[i64]]) ->
Result<text, text>`. Its argument ordering and Result handling match the driver;
the existing wrapper structural spec uses the same production call shape.
No regeneration or executable invocation occurred in this final source check.
Actual old-producer import resolution, compilation and execution remain NOT_RUN.
