# Windows bootstrap: lifetime removal trap and generic rendering receiver loss

Status: focused fixes verified; full bootstrap admission blocked. Source
baseline `0bd5c2`; isolated branch `work/windows-bootstrap-fix-20260928`.

## Continuation: focused fixes verified, full bootstrap admission failed

The C runtime now implements `rt_collection_remove`: tagged array indices
delegate to `rt_array_remove`, while dictionary removal returns the removed
value in one lookup via an optional output on the existing internal delete
helper. The public C `rt_dict_remove` boolean ABI remains unchanged. Unsupported
receivers, invalid indices and missing keys return nil as in the Rust runtime.
No allocation was added to removal. The native owner probe passes, the new C
dispatcher selfcheck passes 18 assertions, and the existing C array/math/UTF-8
twin selfcheck passes all 123 assertions.

Rendering data loss was narrowed beyond the original generic hypothesis:
`expr.symbol` was `x` while even direct `expr.to_latex()` returned `latex:0`.
Cranelift aggregate-copy code ignored resolved `owner_has_vtable` metadata and
copied only 8 bytes from a 16-byte vtable-bearing expression. Both Cranelift
emission paths and recursive field copies now honor resolved true/false layout
metadata, using local vtable lookup only when the metadata is unresolved.

The rebuilt canonical seed is SHA-256
`66a9d0ef540563631d8abd1a65fd2cf86c0f920f101aaa6111b32bed0f3e3b7d`.
An initial generic `T: MathRenderable` helper passed the Cranelift fixture but
still failed LLVM full Stage2 without a concrete expression implementation in
the build: `to_latex` was treated as a method on a builtin receiver. That full
attempt compiled 1,059 files and failed only `rendering.spl`; the owner failure
was cleared. This is a remaining LLVM generic-bound dispatch issue.

The final helper signatures use an explicit `MathRenderable` trait receiver.
Both helpers retain their names and four output formats. The checked-in fixture
`test/fixtures/math_rendering_contract_native/` verifies direct receiver data,
all eight helper outputs, a returned aggregate, and a nested aggregate.
All 11 checks pass under LLVM and Cranelift. The rendering module also compiles
alone under LLVM (2 files), with no concrete expression implementation present.
Focused logs are under `build/mini_builds/win_dynlib_probe/`:
`rendering_trait_llvm1.log`, `rendering_trait_llvm1.run.log`,
`rendering_library_llvm1.log`, `rendering_trait_cranelift1.log`, and
`rendering_trait_cranelift1.run.log`. No unresolved link stubs were produced.

Measured costs: fingerprint 136 seconds; seed build 4m12s; native-all build
3m37s; runtime-noLTO 10.60s; compiler backfill 0.35s. The sampled Rust compiler
peak was 2,926 MiB. Stage2 used 11 memory-admitted jobs from 24 requested, with
a sampled 1,668 MiB process peak and about 10.2 CPU cores averaged during a
713-second sample. These are observed costs, not controlled regression claims.
LLVM fixture link took 4.8 seconds; isolated LLVM module link 3.3 seconds;
Cranelift fixture link 2.9 seconds.

The first full attempt stopped during fingerprinting because the launch
environment carried a backslash-form `CC`; the shell basename check rejected
it. Removing that probe-only override let the pinned LLVM compiler resolve.
Exact environment and outputs are recorded in
`build/mini_builds/win_dynlib_probe/bootstrap-launch-record-20260928.txt` and
`focused-results-c-fixes.txt`. No cache was deleted.

### Final cached Stage2 result

The final strict attempt compiled 3 files, reused 1,057 cached files, and had
zero compilation failures. Compile time was 17.4 seconds and link time was
19.7 seconds (37.1 seconds total). The wrapper admitted 7 jobs from 24 requested
under its memory policy; fingerprinting took 173 seconds and the matching Rust
seed was reused. These timings describe this run, without a controlled baseline.

The linker nevertheless generated 11 unresolved-symbol stubs with
`SIMPLE_NO_STUB_FALLBACK=1`: seven `RtHalIsolatedHostPort` fields
(`bind_adapter_fn`, `cancel_and_reap_fn`, `close_fn`, `current_owner_fn`,
`shutdown_fn`, `spawn_compare_exact_fn`, `spawn_replay_exact_fn`) and
`rt_hal_unavailable_cancel`, `rt_hal_unavailable_effect`,
`rt_hal_unavailable_join`, `rt_hal_unavailable_spawn`. This remains a concrete
linker enforcement defect. Independent review traced this fallback to existing
`linker.rs:2389` and `stubs.rs:1606`, also recorded in the Windows Stage2 CLI
stubs bug report dated 2026-09-25. It is not introduced by this patch. Fatal
stub calls would print and abort; the diagnostic-free exit below does not
establish a stub call. No stub-containing candidate is accepted.

The candidate passed version, arithmetic (`p2_add`), MIR-retention, and
module-path naming checks. Admission failed at `hello-world-positional-build`
with bootstrap mode 0, LLVM backend, and native exit status 1. The bounded
collector reports `reason=child-exit`, 7,400 combined stdout/stderr bytes, and
no timeout. There is no error, panic, or named-trap diagnostic; the last progress
event is `weave_aop` done at 2,365 ms. The RtHal stubs have not been established
as the cause of this frontend failure.

Evidence under `build/bootstrap/windows-linux-20260927/windows/`:

- `console-c-fixes-20260928-final3.log`
- `logs/x86_64-pc-windows-msvc/stage2-native-build.log`
- `stage2/x86_64-pc-windows-msvc/simple.exe.stubbed_symbols.txt`
- `stage3/x86_64-pc-windows-msvc/stage2-sanity.env`
- `stage3/x86_64-pc-windows-msvc/stage2-sanity.env.frontend-bootstrap-0.status.env`
- `stage3/x86_64-pc-windows-msvc/stage2-sanity.env.frontend-bootstrap-0.log.hello-world-positional`

The wrapper verdict is `ABORTED: stage=stage2 exit=2`; the executable was
renamed `simple.exe.rejected`. No newly admitted Stage2 receipt exists, so
Stage3/Stage4 were not run. This scope has reached the three-cycle guard;
further full retries require a new scoped continuation. No production-readiness
PASS or release acceptance is claimed.

The scoped staged direct-env-runtime guard passes and `doc/06_spec` contains
zero executable `_spec.spl` files. The working-tree guard fails on unrelated
materialized CMM/T32 app files; those paths are excluded from this change.
Core/MCP production verification remains blocked by the rejected bootstrap.

### Focused reproduction commands and coverage limits

These are bootstrap-only diagnostic probes, run from the checkout in an x64
MSVC developer shell with LLVM 23.1.1 `clang-cl` selected. The actual focused
launch also sets `SIMPLE_BOOTSTRAP=1`, `SIMPLE_NATIVE_BUILD_RUST=1`,
`SIMPLE_SCV_FREEZE_FALLBACK=1`, `SIMPLE_NO_STUB_FALLBACK=1`, and `SIMPLE_LIB=src`.
SCV fallback is diagnostic only; these passes are not bootstrap admission.

```powershell
$env:SIMPLE_BOOTSTRAP='1'
$env:SIMPLE_NATIVE_BUILD_RUST='1'
$env:SIMPLE_SCV_FREEZE_FALLBACK='1'
$env:SIMPLE_NO_STUB_FALLBACK='1'
$env:SIMPLE_LIB='src'
src/compiler_rust/target/bootstrap/simple.exe native-build --backend llvm --source src/lib --source test/fixtures/math_rendering_contract_native --entry-closure --entry test/fixtures/math_rendering_contract_native/main.spl --cache-dir build/mini_builds/win_dynlib_probe/rendering_trait_llvm1-cache -o build/mini_builds/win_dynlib_probe/rendering_trait_llvm1.exe
build/mini_builds/win_dynlib_probe/rendering_trait_llvm1.exe
```

The Cranelift probe uses the same command without `--backend llvm` and with
`rendering_trait_cranelift1` as the artifact/cache name. The C selfcheck links
the generated full C runtime archive from the verified native owner build:

```powershell
clang-cl /nologo /Gy /Isrc/runtime /Isrc/runtime/platform src/runtime/test/rt_collection_remove_selfcheck.c build/mini_builds/win_dynlib_probe/native-objects-7ddkgS/core_c_runtime/simple_runtime.lib /Febuild/mini_builds/win_dynlib_probe/runtime_remove_selfcheck.exe /link /OPT:REF ws2_32.lib bcrypt.lib advapi32.lib user32.lib shell32.lib ole32.lib dbghelp.lib psapi.lib
build/mini_builds/win_dynlib_probe/runtime_remove_selfcheck.exe
src/compiler_rust/target/bootstrap/simple.exe native-build --source src/lib --entry-closure --entry build/mini_builds/win_dynlib_probe/owner_behavior.spl --cache-dir build/mini_builds/win_dynlib_probe/owner_c_dispatch1-cache -o build/mini_builds/win_dynlib_probe/owner_c_dispatch1.exe
build/mini_builds/win_dynlib_probe/owner_c_dispatch1.exe
```

The archive path is specific to this retained run; a new native build must
use its own generated archive. The existing twin selfcheck uses the same C
link command with `rt_core_c_utf8_math_array_twin_parity_selfcheck.c` and a
distinct output. These fixtures are not wired into a checked-in automated
runner; the owner probe remains a retained build artifact. Cranelift resolved
`Some(false)` and unresolved `None` layout branches lack dedicated regressions.
These are follow-up coverage gaps, not claimed passing acceptance criteria.

## Superseded initial investigation (historical evidence)

The sections below preserve the original failing evidence from the first
scope. Statements about reverted contracts, unimplemented removal, and no
subsequent Stage2 run describe that earlier point and are superseded by the
continuation results above.

## Lifetime owner array removal

The existing owner update callback loses its `_DynlibLifetimeStateV1` type
during bootstrap HIR lowering (`i64.entries`). Direct mutex-protected typed
state operations compile successfully in the focused native build:
`build/mini_builds/win_dynlib_probe/direct_all_1.exe`.

A native behavior probe at
`build/mini_builds/win_dynlib_probe/owner_behavior.spl` loads `kernel32.dll`,
registers its handle, begins two uses, retires it, verifies that a retired
identity rejects new borrows and repeated retirement, and ends both uses.
The final use calls array `.remove(index)` and aborts with:

    simple runtime: unimplemented runtime entrypoint `rt_collection_remove` was called.
    This is a NAMED TRAP stub, not an implementation.

Exit: `-1073740791`. Native compile/link succeeded without unresolved link
stubs. Both the existing `next.entries.remove(index)` and a temporary explicitly
typed local `var entries: [_DynlibLifetimeEntryV1] = next.entries` reproduce
the trap. The unsuccessful local-variable change was reverted.

Evidence: `owner_behavior1.log`, `owner_behavior2.log` and corresponding
executables in `build/mini_builds/win_dynlib_probe/`. Probe 2 compiled three
files and linked in 4.3 seconds. `src/runtime/runtime_native.c` implements
`rt_array_remove`; `rt_collection_remove` is a named trap. Investigate
bootstrap method lowering to the actual array removal primitive. Do not
replace the trap with a success stub or accept compile-only evidence.

## Generic rendering receiver

`src/lib/nogc_sync_mut/src/math/rendering.spl` has untyped expression parameters
whose `to_latex()` calls fail full bootstrap compilation. A proposed explicit
`MathRenderable` trait with four required text-returning methods and generic
`render_all<T: MathRenderable>(expr: T)` / `render_as<T: MathRenderable>`
helpers compiles, but loses receiver data at runtime.

Fixture: `build/mini_builds/win_dynlib_probe/behavior.spl`. Its expression
contains `symbol: text` initialized to `"x"`. Each implementation returns a
format prefix plus `self.symbol`. Expected `latex:x`, `mathml:x`, `text:x`,
`lean:x`; observed `latex:0`, `mathml:0`, `text:0`, `lean:0`, followed by the
probe failure and exit 1. Evidence: `behavior3.log` and `behavior3.exe` in the
same directory. Five files compiled; link completed in 3.4 seconds without
unresolved stubs. The proposed source contract and test were reverted because
this behavior is not correct. Preserve both public rendering helper APIs when
fixing the underlying type/receiver lowering.
The rejected contract is saved as `rendering_candidate.spl` beside the probe;
reproducing its run requires that candidate at the imported rendering module
path in an isolated checkout. The checked-in rendering module remains original.

The first probe also exposed an unresolved `assert` being link-stubbed despite
`SIMPLE_NO_STUB_FALLBACK=1`; subsequent probes define their own assertion
function and contain no unresolved link stubs. This illustrates why native
execution and fail-fast assertions are necessary.

## Performance assessment and verification limits

The direct-lock owner change preserves one lock/unlock pair per operation,
binary-search lookup (O(log n)), bounded capacity 4096, and O(n) array removal.
Native library unloading remains outside the mutex. No measured runtime
speedup is claimed. The runtime trap prevents meaningful end-to-end lifetime
timing; correctness must be restored before benchmarking that path.

No full Stage2 retry or Stage3/Stage4 run was started after these findings.
No release or production-readiness PASS is claimed. Existing native caches
and earlier full-bootstrap evidence remain intact. Further retries stopped
under the repository's bounded verification guard.
