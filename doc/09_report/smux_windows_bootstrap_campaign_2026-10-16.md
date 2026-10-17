# Windows smux compiler rebuild campaign

Source: immutable detached worktree `D:/dev/simple-smux-bootstrap-20261016`, commit `f612b3f68d6fc315b44df0cff8ec8a6f1db0f5da` (reviewed smux feature and MIR fix). Previous frozen source and producer evidence remain untouched.

Reason: prior exact Phase 2 producer emitted a caught LLVM codegen failure in `smux_pane_spawn_pty` from erroneous transfer-envelope lowering. That binary cannot contain the reviewed MIR owner/symbol fix. Rebuilding the compiler, then compiling smux with its actual bytes, is necessary. Rust is permitted only as the canonical bootstrap producer; application and test claims must use the resulting pure-Simple phases.

Finite dependency graph:

1. Canonical Stage 2 trust-root rebuild/admission, with canonical seed/runtime preparation and phase qualification.
2. Compile and execute real Hello with the exact new Phase 2 compiler; record compiler/output hashes and expected stdout/exit.
3. Phase 2 smux focused native build against the reviewed source; preserve source-qualified capsule caches and all actual failure diagnostics.
4. After actual Hello succeeds and canonical planner admission exists, enter the requested Stage 3 continuation. Repeat its own Hello compile/run before dependent application evidence. Compiler-only phases never stand in for a general SSpec/docgen runner.

Initial checked prerequisites: native Windows 11 Pro 10.0.26300 x64; Git Bash `C:/dev/tool/Git/bin/bash.exe`; LLVM prefix `/c/dev/tool/clang+llvm-23.1.1-x86_64-pc-windows-msvc`. The canonical PATH-access fixture passed all ten cases (`build/smux-windows-bootstrap/path-fixture.stdout.log` in the new worktree). One backend job was selected, with normal canonical resource and admission checks retained. Rust authority generations and leases are owned by the canonical wrapper; none were copied from another session. No other-session source/cache was changed.

## Initial startup failure and supported correction

First invocation used the default centralized output. It exited before compilation: `VERDICT — ABORTED: stage=starting exit=1 signal=none reason=starting`, preceded by `materialize-symlinks-windows: receipt must use the dedicated bootstrap output root`. Logs: `build/smux-windows-bootstrap/campaign.stdout.log` and `campaign.stderr.log` in the new worktree.

Source inspection found an incompatibility: `scripts/bootstrap/lib/centralized-storage.shs` defaults output below `.simple/storage/build/bootstrap`, while `scripts/setup/materialize-symlinks-windows.shs:418` permits in-repository receipt paths only below `build/bootstrap/`. The documented absolute `--output` override selects an allowed dedicated descendant; bare `--output=build/bootstrap` would be remapped to the centralized default. No materializer or admission check is bypassed.

Corrected command, run from the immutable worktree:

```sh
bash scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --stop-after-stage2 --backend=llvm --mode=dynload --jobs=1 --keep-going --produce-stage3-receipt=verify-reviewed-compiler-fix --output=/d/dev/simple-smux-bootstrap-20261016/build/bootstrap/smux-campaign --progress
```

This is the documented receipt-free Stage 2 trust-root lane, followed by the canonical planner receipt producer bound to the admitted new parent. `--full-bootstrap --stop-after-stage3` is not receipt-free and is not used to circumvent that dependency.

Corrected campaign native parent PID: **756**; tool execution session: **79327**. At the first follow-up observation its Bash child PID 8680 was live and materialization had begun. Launch script and PID/status/stdout/stderr are retained in `D:/dev/simple-smux-bootstrap-20261016/build/smux-windows-bootstrap/` with the `campaign-attempt2` prefix. The owner monitors every 30 seconds and reaps the owned tree if its 7200-second outer campaign limit expires; canonical per-row checks remain enabled. No compiler, Hello, smux, Stage 3, or SSpec PASS is claimed while this campaign is running.

Follow-up live evidence: the corrected campaign passed Windows source materialization and native C admission (`bootstrap-windows-c-admission ... status=0`), found LLVM 23 shared provider `LLVM-C.dll`, and entered canonical Rust seed/runtime construction. At observation native Cargo PID 23188 and rustc PID 22772 were live; the canonical progress journal reported `milestone=rust-rust-seed-build`, `terminal=running`, eight tree processes and approximately 347 MB tree RSS. Authority staging root is `build/bootstrap/smux-campaign/rust-authority-75ad980a33be1ccc4bc84fa26d54327ff6b2124908a7ca0d17d835094312cdc3`. The campaign remains under the same native parent PID 756 / tool session 79327; these are live observations, not a compiler admission or completed seed claim. Continue observing the same owner; do not restart because a tool observation yields or expires.

## Prepared downstream Windows product composition

The editing checkout now contains additional native Windows providers and smux features that are intentionally absent from the active immutable f612 compiler snapshot. After the rebuilt pure-Simple producer qualifies, freeze those final product bytes in a separate checkout/commit and compile that source with ordered roots: **`src/providers/windows_native/lib` first**, then `src/os`, `src/lib`, and `src/app/hosted_apps`. The `lib` suffix is necessary: it is the root used by the source-selection contract. This selects the public `std.sys.pty` and synchronous `std.nogc_sync_mut.sosix.network` overlays while retaining original SFFI HTTP/UDP providers. Explicit root-order tests are authored; source review is not their execution.

Prepared argument shape (template; not yet executed): `<admitted-phase2-or-phase3-compiler> native-build --source src/providers/windows_native/lib --source src/os --source src/lib --source src/app/hosted_apps --entry-closure --entry src/app/hosted_apps/smux_client.spl --backend=llvm --runtime-path <matching-frozen-runtime-authority> --cache-dir <private-producer-and-product-cache> --output <private-smux-output>`. Bind the actual admitted compiler hash, product commit, source-root order, matching runtime bytes, toolchain and output/cache paths before launch. The Windows native linker owners already include `kernel32.lib` and `ws2_32.lib`; this is source evidence only and does not establish successful ConPTY/TCP linking or runtime behavior.

Consume the exact canonical Stage 2 Hello compile/run receipt if the campaign has already produced it successfully for these compiler bytes; do not repeat that unchanged green acceptance gate. If it has not, run the smallest real Hello compile and execute its resulting binary once, recording actual stdout and exit. Phase 3 may start provisionally only after that actual gate, and must separately acquire canonical admission before formal qualification. No Rust seed application tests and no general SSpec execution on compiler-only phases are permitted.

## Canonical Stage 2 construction reached

The same corrected campaign progressed to `Stage 2: admitted parent → bootstrap_main.spl`. Canonical Rust seed, native-all runtime, and compiler-backfill build logs each ended `native_process_status=0 shell_status=0`. The published Rust authority current marker records generation `75ad980a33be1ccc4bc84fa26d54327ff6b2124908a7ca0d17d835094312cdc3-669fe18cff33251319460c404e09fa42085092ceac7c2b5296fc1e02676f2240`, generation hash `669fe18cff33251319460c404e09fa42085092ceac7c2b5296fc1e02676f2240`, stamp hash `14957329744b6865862b5e21e31a4db813b395a597c4a964ee3a047409e35331`. Exact Rust seed SHA-256 is `9a9a921edf3d1675fc763aad9ff0adaac6be04358b889ff5d0e15e1b8c78a47e` (17,630,720 bytes). This identifies the bootstrap producer only; it is not an application/test runner substitution.

Actual Stage 2 native builder PID 23692 was live at campaign elapsed approximately 5066 seconds, CPU 2146 seconds, RSS approximately 616 MB. Its private staging `build/bootstrap/smux-campaign/stage3/x86_64-pc-windows-msvc/native-objects-yLqywb` contained 867 actual `.o` files totaling 21,447,104 bytes; latest `mod_866.o` was written at 11:11:14 local time. This demonstrates compiler construction progressing; the final Stage 2 executable and its Hello/admission gates were still pending. Observe the same owner/session, preserve this staging/cache, and do not restart solely because an observation handle yields.

Downstream product source has now been frozen independently: commit `270d5b30a1acc77fc6157e6202dd1d48934948a7`, clean checkout `D:/dev/simple-smux-product-270d5b30a1a` supplied by the merge owner. It includes Windows TCP/ConPTY/native console overlays and the reviewed interactive application changes. The active compiler source remains f612; no product files are copied into it. After producer Hello/admission, use the ordered four-root recipe above against that exact product checkout. Native `user32` clipboard linkage remains an observed-at-link gate; presence in some broader default linker lists does not prove this selected product path links it.

## Terminal canonical result: Stage 2 link failure

Campaign attempt 2 ended normally with **exit 1**, before the 7200-second outer limit: `VERDICT — ABORTED: stage=stage2 exit=1 signal=none reason=stage2`. The compiler rebuilt 1349 modules; final linking failed with `lld-link: error: undefined symbol: __simple_pow`, referenced by `libspl_objects.a(mod_493.o):(compiler__mir__mir_instruction_graph__mir_fold_binop)`. No Stage 2 executable or Hello/admission exists. Owner PIDs 756, 8680 and builder 23692 were absent in the terminal process query. The canonical Windows Job receipt independently records `status=complete`, `exit_status=1`, `quiescent=1`, `containment_scope=win32-job-object-no-breakaway`, `root_exit_raw=0x1`, peak RSS 1,273,400 KiB. Original logs and nonpassing receipts are preserved.

Quiescent retained staging `build/bootstrap/smux-campaign/stage3/x86_64-pc-windows-msvc/native-objects-yLqywb` contains 1351 `.o` files (1349 modules plus retained main/init C objects), 30,162,846 bytes, and `libspl_objects.a` of 34,907,930 bytes. No archive was overwritten. The existing-runtime TU manifest omission was assigned to the compiler owner; a reviewed source fix is separate from this immutable f612 campaign.

`llvm-nm` 23 found no `__simple_pow` definition in any of the three inspected original archives: supplemental core C `simple_runtime.lib` SHA-256 `6843a4be7133204a22d0a16b249799beb091f6b37060f14e64d1e6dac6f21aaf`; authoritative `deps/simple_runtime.lib` SHA-256 `b56d167a5b531d033ae3c94848c3324a11dcef5263f2d2bc3574791887710807`; authoritative `simple_native_all.lib` SHA-256 `1be0f06bd363f781a927566758233ebd8a62051cddb2c9ef35c99c2857eadf51`. `mod_493.o` contains the undefined reference.

A separately authorized diagnostic compiled the existing frozen `runtime_core_intrinsics.c` once to private `build/smux-windows-bootstrap/diagnostic-relink/runtime_core_intrinsics.obj`: compile exit 0, 3478 bytes, SHA-256 `99452f7eb3c1642aa787c1717b317d306248d2daa27fd92ef5be6e59881ad1dd`. Full args, stdout/stderr, definition scans and archive collision scans are retained beside it. The exact compiler is frozen LLVM 23 `clang-cl.exe`, SHA-256 `d43b7fa07b5b77b716e60600ad2792cfb2eeb370aecb6144bf6c698f2c6d7467`. The GNU-style compile flags match the frozen source branch: `cc_detect::is_msvc_compiler` recognizes only `cl`/`cl.exe`, so the C-runtime builder takes its non-MSVC arm for `clang-cl`; the separate atomics-flag helper recognizes `clang-cl` and adds the two MSVC C11 flags. Pinned MSVC INCLUDE/LIB values came from the original recorded Rust command environment.

Collision audit is not universally clear: original Rust runtime archives already define strong `__simple_intrinsic_bounds_check`; common `fprintf`/`__local_stdio_printf_options` overlaps also occur. Existing canonical link policy already uses `/FORCE:MULTIPLE` for the native-all/core-C composition and rejects unresolved symbols. Any diagnostic relink must retain that existing policy, prove actual bounds-check ownership/extraction, and must not add `/FORCE:UNRESOLVED` or strip/localize symbols blindly. Original link argv was not captured because verbose was disabled; the forthcoming relink argv must explicitly be labeled **reconstructed from source and retained inputs**, never captured original argv. There is no diagnostic candidate or Hello result yet.

## Prepared native fixture watchdog

After the exact diagnostic compiler passes real Hello compile/run, each separately compiled native fixture can use the existing canonical Windows Job supervisor, from the frozen product checkout, with a fresh evidence row:

```sh
perl /d/dev/simple-smux-bootstrap-20261016/scripts/resource/process-tree-rss-watchdog.pl --session-mode=new --max-rss-kib=5859375 --rss-cap-mode=enforce --interval-ms=100 --timeout-seconds=180 --term-grace-seconds=1 --receipt=/d/dev/simple-smux-product-270d5b30a1a/build/smux-native-evidence/PRODUCER/FIXTURE.job.env -- /absolute/FIXTURE.exe /absolute/smux.exe
```

The last application operand is supplied only to fixtures that require the real product binary. The canonical Perl owner compiles/adopts its existing `bootstrap-session-exec.c` helper, pins identities, starts a no-breakaway Windows Job, enforces the 180-second workload deadline and records actual exit plus full-tree quiescence. Require `observer_backend=win32-job-object`, `containment_scope=win32-job-object-no-breakaway`, `quiescent=1` and the expected fixture exit; timeout is `status=timeout`/exit 124, containment/helper failure is a failure (not a passing timeout). Retain full fixture stdout/stderr and the Job receipt. This recipe is prepared only; no fixture smoke was run before the new producer's Hello gate.


Prepared reconstructed diagnostic argv is retained as `build/smux-windows-bootstrap/diagnostic-relink/reconstructed-link.args.json` and a single-line Clang response file. It preserves retained `_main_stub.o`/`_init_all.o`, NativeAll-before-core-C archive order, 212 actual module-init roots extracted from the module archive (excluding the generic dynamic initializer), three source-derived runtime retention anchors present in NativeAll, all 27 frozen Windows platform libraries, and the exact LLVM 23 compiler builtins/LLVM-C import libraries. It adds a private one-member `intrinsics-helper.lib` after the existing runtime archives and a MAP output; original `/FORCE:MULTIPLE` and `/errorlimit:0` remain, with no unresolved-symbol relaxation or added strip policy. The private helper archive SHA-256 is `51a7d2e67086c6ea7098ffe652f58bd57fe33dfc3211172e11798ce2c9b3b433`. Actual original module/init/archive bytes were hashed into `original-inputs.sha256` (1352 input paths).

A Clang `-###` dry run of that single-line response file exited 0 and selected LLVM 23 `lld-link`, target x86_64-pc-windows-msvc. An earlier multiline response-file layout was rejected by Clang's `/link` line handling and is preserved separately; it did not execute a link. The source-derived recipe is undergoing independent review before actual candidate construction. No candidate/Hello or downstream fixture outcome is claimed.

## 2026-10-17: remote integration and actual diagnostic outcomes

The editing source is now isolated at `D:/dev/simple-smux-upstream-20261017`,
based on fetched `origin/release_phase3` revision
`e37c260fe5dfa6d1fdb23ef0793a11999b548d4f`. The reviewed smux changes were
cherry-picked there. Remote commit `677b77f29073a1c1805299919b19668bfee2e0f9`
already supplies `runtime_core_intrinsics.c` in the bootstrap manifest;
integration commit `7a2fa6eee23` removes the duplicate introduced by combining
the repairs. The private-header fingerprint dependency and actual archive ABI
regression remain. Commit `5be1e7e7578` carries the ordered native test source
selector and shared-client fixture. No frozen producer/source was updated.

The source-reviewed reconstructed diagnostic link ran under the existing
180-second Windows Job supervisor. `root-link.job.env` records complete,
exit 0, quiescent 1. The resulting `simple-diagnostic.exe` is 22,857,216 bytes,
SHA-256 `bad4c7fced5d4c945a24a3deb8f601685446a76dbbe2ace5938feeccaea1b04a9`.
`simple-diagnostic.map` identifies exactly one `__simple_pow` public owner,
`intrinsics-helper:runtime_core_intrinsics.obj`. The bounds-check overlap has
a duplicate warning but no public MAP entry; dead stripping is an inference,
not proof of a surviving body. This binary is diagnostic and unadmitted.

Three actual Hello compile attempts are retained under
`build/smux-windows-bootstrap/diagnostic-relink/` in the frozen checkout:

| Evidence prefix | Changed input | Actual result |
| --- | --- | --- |
| `root-hello-build` | Initial diagnostic producer | Exit 1: SCV compile-event journal missing |
| `root-hello-cold-build` | Supported `SIMPLE_SCV_INVENTORY_COLD_INIT=1` | Parse/HIR 1/1, then exit 1: native-all has unresolved LLVM APIs |
| `root-hello-llvm-build` | Same cold-init policy plus exact pinned `LLVM-C.lib` through LINK | Parse/HIR 1/1, then exit 1: relocations against discarded `rt_value_print`/`rt_value_println` sections |

The latter two Job receipts record complete, exit 1 and quiescent 1. They
are linker failures, not observation timeouts. Full commands, logs, selected
environment and import-library hash are retained beside the launch scripts.
The LLVM injection is diagnostic only; canonical source must stage and validate
the exact producer dependency through its runtime authority. Astra is reviewing
the newly exposed C/Rust provider collision separately.

Those three attempts produced no Hello output executable. The canonical f612
campaign remains failed; subsequent diagnostic evidence is separate below.

## Diagnostic Hello gate passed with reviewed ABI forwarding

Astra inspected the actual retained COFF sections and alias relocations.
The Rust `rt_value_print`/`rt_value_println` forwarding exports share sections
with `rt_print`/`rt_println`. The selected C raw-string functions discard those
Rust sections and strand the otherwise unique aliases. Reordering archives
would change raw-string versus tagged-value ownership. Instead, the reviewed
private `tagged-print-alias-shim.c` forwards the two aliases to the already
selected C `rt_print_value`/`rt_println_value`, preserving their actual call
targets without a new printing algorithm or linker relaxation.

`root-hello-alias-build.job.env` records complete, exit 0, quiescent 1 and
peak RSS 3,412,368 KiB. The produced `root-hello-alias.exe` then ran under
`root-hello-alias-run.job.env`: complete, exit 0, quiescent 1, peak RSS 2,560 KiB,
stdout exactly `windows native hello` plus newline, empty stderr. Actual
compiler/output hashes are in `root-hello-alias.output.sha256`; shim source,
object and import-library hashes are in `root-hello-alias.inputs.sha256`.
This is the first real diagnostic Hello compile/run success, not canonical
admission. The initial shim compile exposed Git Bash slash-option conversion;
that failed log is retained, and the corrected command uses dash options.

The same reviewed shim/import-library composition now builds the frozen
`270d5b30a1acc77fc6157e6202dd1d48934948a7` product under
`D:/dev/simple-smux-product-270d5b30a1a/build/smux-diagnostic-phase2/`, with
ordered provider roots and an existing no-breakaway Windows Job watchdog
(600 seconds, 5,859,375 KiB RSS ceiling). At this entry the build is live, not
a product PASS. Phase 3, native fixture, SSpec and docgen evidence remain absent.

The canonical C forwarding exports and a mixed-runtime C ABI fixture are
authored in the integration tree. Initial mixed tests incorrectly enabled
`SIMPLE_CORE_C_STANDALONE` while linking native-all. Astra traced the resulting
Vulkan alias errors to the C host-target getter enabled by that flag; this
was a diagnostic recipe defect, not a remote Vulkan source regression. No
Vulkan exports or archive-order changes were added.

The corrected mixed test compiles the original 32 selected C TUs (the current
integration source for `runtime_native.c`, frozen originals for the others)
with native-all's MSVC flags `/c /O2 /Gy /MD /std:c11` and
`/DSIMPLE_RUNTIME_MEMORY_OWNER=1`, without standalone/dynload defines. It links
those real objects with the retained native-all archive and exact LLVM import
library. `tagged-print-native-all-link.job.env` and
`tagged-print-native-all-run.job.env` both record complete, exit 0, quiescent 1.
Actual stdout matches the authored ABI fixture's expected output after CRLF
normalization; stderr is empty. The fixture exercises raw C-pointer printing,
nil, positive/negative integers, booleans and C-created tagged strings. The MAP
identifies all six print names in the actual patched C runtime object.
This does not establish Rust-created heap string interchange or a full runtime
admission. No passing check was rerun.

The first frozen-product smux diagnostic is now terminal: complete, exit 1,
quiescent 1, peak RSS 2,080,916 KiB. It parsed 115 modules and completed HIR for
114, then refused `src/lib/nogc_sync_mut/io.spl` with `module
std.nogc_sync_mut.io has no exported item rt_debug_set_active`. The aggregate
HIR failure blocked backend/publication, so there is no smux executable. This
is not a timeout or a runtime feature verdict. A direct owner-export repair
and a real facade/state regression are assigned separately.

The scoped print repair is now merged through PR #3609 into `release_phase3`,
merge `8bcff950fa620af8af3ec313112a08407db71ca7`. Its isolated exact head was
`0ccaf2bc4c1e12b6a1a48523b87ef776b72eb4c7`, matching the reviewed source bytes.
No publication or release tag was created. The larger smux PR remains draft.

Integration checkpoint `28f6ee14653` fixes the I/O concrete owner export and
adds a real state getter/fixture. Its actual bounded regression cleared HIR
76/76 with zero failed/unfinished modules, then timed out before output
publication (124, quiescent 1). There are no native object/ICE artifacts in that
row and no executed state-transition PASS. Checkpoint `be59642abc6` stages
the producer-pinned LLVM import dependency and validates combined actual link
inputs before deduplication in both MSVC routes. Astra accepted both source
repairs. Shell syntax and byte-custody tests passed; five Simple selector
scenarios and canonical native qualification remain unexecuted.
