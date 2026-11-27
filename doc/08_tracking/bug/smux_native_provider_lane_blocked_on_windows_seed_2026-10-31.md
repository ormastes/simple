# smux live-host specs blocked: no Windows native provider under the seed

Status: OPEN. Host: Windows 11, `build/caret/seed-fixed2.exe`, branch
`work/release-caret-cmux-20261031`. These specs are correct and stay RED.

## Root cause

The seed runs specs in the interpreter, which resolves `std.sosix.pty` to the
legacy `src/lib/sys/pty.spl`: `can_resize()` is false (:94), `spawn_configured_v1`
returns Err (:21), `literal_bytes_supported_v1()` is false (:31). The real provider
is the overlay `src/providers/windows_native/lib/sys/pty.spl` (`can_resize` true at
:51), built on raw kernel32 externs in `src/lib/nogc_sync_mut/io/windows_pty_abi.spl`
that only link in a native compile. The seed runtime's `rt_pty_*` has no resize.

Any geometry change with a live PTY child therefore refuses at
`src/os/apps/smux/window_layout_service.spl:248`:
`terminal layout requires native resize capability`. Measured for
`smux_split_pane`, `smux_arrange_window`, `smux_select_layout` and
`smux_set_pane_border`.

The native lane that would select the overlay cannot run here:

- `doc/03_plan/sys_test/smux_major_features_phase3.md:82` requires
  `native-build --library-mode nogc-sync-mut`; `src/compiler_rust/driver/src` has
  no `library-mode` flag.
- `native-build` of a three-line hello panics in the seed, with and without
  `--backend llvm`: `TryFromIntError(PosOverflow)` at
  `vendor/cranelift-jit/src/backend.rs:307` (seed-fixed2) and
  `compiled_blob.rs:58` (seed-fixed). See "Seed bugs".
- Earlier Windows smux native builds are separately recorded as blocked:
  `windows_smux_native_build_memory_budget_2026-10-17.md`,
  `smux_windows_phase2_cold_build_timeout_2026-10-16.md`.

## Specs

All paths are under `test/03_system/tools/`.

| Spec | Failing point | Unblock condition |
|---|---|---|
| `smux_window_rename_spec.spl` | :141, split with a live child refuses | native provider in the spec process |
| `smux_windows_conpty_features_spec.spl` | :132, `select_layout` refuses | same |
| `smux_interactive_windows_input_spec.spl` | :26, `select_layout` refuses | same |
| `smux_zoom_spec.spl` (native case) | :313-315, split/arrange refuse | same |
| `smux_presentation_native_spec.spl` (first case) | :107-117, border change refuses | same |
| `smux_literal_input_spec.spl` | :119-120, no literal provider or child | same, plus `SIMPLE_TEST_LITERAL_CHILD` = compiled `test/fixtures/coremux/literal_input_child.spl` |
| `smux_configured_launch_spec.spl` | :124-127, :137-140 | same, plus `SIMPLE_TEST_CONFIGURED_CHILD` = compiled `test/fixtures/coremux/configured_launch_child.spl`, `SIMPLE_TEST_CONFIGURED_CWD`, `SMUX_CONFIGURED_REMOVE`, `SMUX_CONFIGURED_KEEP` |
| `smux_windows_owner_lifecycle_spec.spl` | `SMUX_TEST_BINARY` unset | compiled `smux.exe` |
| `smux_windows_shared_clients_spec.spl` | `SMUX_SHARED_CLIENTS_FIXTURE`, `SMUX_TEST_BINARY` unset | compiled fixture and `smux.exe` |
| `coremux_sosix_endpoint_spec.spl` | :30 `TEST_BLOCKED` | framed server plus `SIMPLE_TEST_COREMUX_PORT`, `_AUTH`, `_NAMESPACE`; no script in `scripts/` starts it |

A search of `scripts/`, `.github/`, `test/fixtures/`, `doc/03_plan`, `doc/05_design`
and `doc/08_tracking/bug` for these variables matched only
`doc/03_plan/sys_test/smux_windows_phase3_features.md`, a manual procedure that
names `SMUX_TEST_BINARY` and `SMUX_SHARED_CLIENTS_FIXTURE`. Nothing automates them.

## Resolved RED: split UTF-8 fragments

`smux_client_input_spec.spl` cases "should preserve UTF-8 byte fragments split
inside a scalar" and "should forward a prefixed unknown binding split inside its
Unicode scalar" fed `bytes_to_text(bytes[0:1])`. `rt_bytes_to_text` is lossy before
the decoder sees the input: `interpreter_extern/conversion.rs:192` and
`runtime/src/value/sffi/file_io/file_ops.rs` both use `String::from_utf8_lossy`.
Measured: a one-byte fragment reads back as `[239, 191, 189]`.

Owner decision: text stays UTF-8. `client_input_feed` and the console `read`
capability now carry `[u8]`. The input wire still admits only complete UTF-8
(`interactive_protocol.spl` `smux_input_hex_decode`), so `client_input_wire_split`
holds an incomplete tail in the client until its scalar completes.

Runtime disagreement, noted and not changed: the C runtime's `rt_bytes_to_text`
(`src/runtime/runtime.c:4236`) preserves bytes while the Rust runtime replaces them
with U+FFFD. Malformed console bytes therefore reach the wire as U+FFFD under Rust,
and as raw bytes the server refuses under C. Only the Windows provider exists today
and it emits valid UTF-8, so this is not reachable yet.

## Seed bugs

1. Chained `me` methods write the result into the root receiver. Unfixed in the
   seed, worked around in smux by declaring pure builders as `fn`. Suspected site:
   `compiler/src/interpreter/expr/calls.rs` around :296-308.

   ```
   class C:
       a: i64
       n: i64
       me ma(x: i64) -> C:
           return C(a: x, n: me.n)
       me mn(x: i64) -> C:
           return C(a: me.a, n: x)
   val c = C(a: 1, n: 1)
   val r = c.ma(2).mn(3)
   # c is now (2, 3); expected (1, 1). fn.fn, fn.me, me.fn and a single me call are safe.
   ```

2. `"nope".to_int()` and `"1x".to_int()` return 0, so `?? default` never fires.
   Multi-character parse failure in `interpreter_method/string.rs` around :421. Other
   smux sites using `.to_int() ?? <nonzero>` may carry the same assumption;
   `pane_io_service.spl` was fixed by `pane_csi_forward_count`.

3. Seed `native-build` panics on Windows for any entry (see above). Repro:
   `seed native-build --source src/lib --entry-closure --entry hello.spl --output hello.exe`.

4. `rt_bytes_to_text` disagrees between runtimes, as above.

## Native-build attempts recorded 2026-10-31 (unblock condition)

A hello-world `native-build` on this Windows host failed both ways; neither is evidence for the native lane.

- Seed from this branch, sha256 `7005d1119c1d299f`: panics at vendored `cranelift-jit/src/backend.rs:307`, `i32::try_from(what - at)`, because the PLT and GOT land more than 2 GB apart.
- Stage 3 from another lane's worktree, built 2026-10-25, sha256 `13d73267e690b2cd`, with LLVM 23 and the MSVC env: `lld-link: undefined symbol: rt_proc_start_time`, referenced by `rt_process_start_identity`. Its runtime source list predates the current tree. A Stage 3 is not a Stage 4 substitute in any case.

Unblocks when a Windows Stage 4 full CLI from this source exists (bootstrap lane, PR #5540), or the seed's JIT keeps PLT and GOT within 2 GB.

## Native lane update, branch work/relfix-native-20261031 (2026-10-31)

Fixed on this branch: the JIT panic (per-module arena, vendor patch in
`vendor/cranelift-jit/src/memory.rs`), ConPTY stdio inheritance, surrogate input on
VK_MENU key-up, `PaneRecord` aliasing, C `rt_random_hex` ABI, native
`to_start_with`/`to_end_with`, and family re-export lookup.

Recipe used. It is not the sanctioned lane; the specs ran as plain native-built
executables, not through a test runner:

    export SIMPLE_MINGW_ROOT=<llvm-mingw-ucrt>
    . scripts/setup/windows-gitbash-bootstrap-env.shs
    # cwd = a staged copy of src/{lib,app,os,compiler} with
    # src/providers/windows_native/lib copied over src/lib
    SIMPLE_NATIVE_BUILD_RUST=1 seed native-build --source src/app --source src/lib \
      --source src/os --source src/compiler --entry <spec> -o <spec>.exe

`SIMPLE_TEST_CONFIGURED_CWD` must be a backslash path containing a space and Hangul.

### Open

1. `--source src/providers/windows_native/lib` does not select the overlay in the seed
   native-build: `std.sys.pty` still resolves to `src/lib/sys/pty.spl` and the link
   reports undefined `rt_pty_*`. The staged tree above is a workaround for this gap.
2. Native callers get a corrupted result from the console `open` once the PTY facade is
   in the closure. Inside `windows_console_open_v1` the handle is 1; the caller's
   `opened.unwrap()` is a varying 32-bit value, so the first write fails with `invalid or
   closed console lease`. Importing `std.sys.terminal_console` directly fails the same
   way. Cause not found. Preferring the exact import owner in
   `named_callable_return_type` did not change it. Blocks `smux_windows_shared_clients`
   (fixture exit 17) and any smux client attach built this way.
3. `rt_driver_*` and `rt_package_*` do not link in this lane. `pane_backend.spl` uses
   `std.nogc_async_mut.sosix` and `package_sffi`, so `pane_backend_spec` and
   `pane_backend_windows_spec` cannot build natively.
4. `smux_windows_owner_lifecycle`: "delayed output beyond pipe capacity" failed in 2 of
   3 runs and "keep another session responsive" in 3 of 3. Not investigated.
5. `smux_presentation_native` failed once in 4 runs on the final seed, on a host with
   little free memory. Not investigated.
6. A spec built directly with `--entry` exits 0 even when examples fail. Read the
   `N examples, M failures` line.
7. Default `native-build` (no `SIMPLE_NATIVE_BUILD_RUST`) now gets past the panic, then
   `build_memory_start_refusal_v1` refused it at 8.8 GiB and 3.6 GiB headroom. Hello has
   not completed on that path.
8. `llm_caret_cli_cached`, `llm_caret_cli_hidden_cached` and `llm_caret_native_closure`
   require a self-hosted runtime and reject seed-built artifacts by design. They need a
   Stage 4 binary. `llm_caret_messaging_phase_cli` was not run.
