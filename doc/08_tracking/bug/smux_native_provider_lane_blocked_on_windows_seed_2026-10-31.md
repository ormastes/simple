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

## Separate RED: split UTF-8 fragments

`smux_client_input_spec.spl` cases "should preserve UTF-8 byte fragments split
inside a scalar" and "should forward a prefixed unknown binding split inside its
Unicode scalar" feed `bytes_to_text(bytes[0:1])`. `rt_bytes_to_text` is lossy before
the decoder sees the input: `interpreter_extern/conversion.rs:192` and
`runtime/src/value/sffi/file_io/file_ops.rs` both use `String::from_utf8_lossy`.
Measured: a one-byte fragment reads back as `[239, 191, 189]`. No `.spl` change can
recover it. Unblock: byte-preserving text in the runtime, or an owner decision to
move the decoder's contract to `[u8]`, at which point the spec changes with it.

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
   smux sites using `.to_int() ?? <nonzero>` carry the same assumption, such as
   `pane_io_service.spl:120`.

3. Seed `native-build` panics on Windows for any entry (see above). Repro:
   `seed native-build --source src/lib --entry-closure --entry hello.spl --output hello.exe`.

4. `rt_bytes_to_text` is lossy, as above.
