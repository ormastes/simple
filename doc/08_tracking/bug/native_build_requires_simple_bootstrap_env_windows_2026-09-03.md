# native-build fails on hello world unless SIMPLE_BOOTSTRAP=1, and says nothing useful

Date: 2026-09-03
Host: Windows 11, MSVC ABI, `. scripts/setup/windows-msvc-bootstrap-env.shs` sourced.

## Summary

`native-build` of a two-line hello world FAILS on every Windows compiler binary
on this host unless `SIMPLE_BOOTSTRAP=1` is set. The failure message is
corrupted, so nothing points at the cause. Bisected to that ONE environment
variable.

## Repro

```
printf 'fn main():\n    print("hello")\n' > h.spl
```

| binary | invocation | result |
|---|---|---|
| `stage3/.../stage2-admitted/simple.exe` | bare `native-build h.spl -o h.exe` | rc=1 `AOT compile error in h: <invalid-heap:0x...>` |
| `build/bootstrap/stage2/x86_64-pc-windows-msvc/simple.exe` | bare | rc=1 same `<invalid-heap:...>` |
| `bin/simple.exe` | bare | rc=1 `native-capsule-receipt-invalid:h` |
| `stage3/.../stage2-runtime-authority/simple.exe` | bare | rc=1 `native-capsule-receipt-invalid:h` |
| `stage3/.../stage2-admitted/simple.exe` | full flags + `SIMPLE_BOOTSTRAP=1` | rc=0, `./h.exe` prints `hello`, rc=0 |
| same, identical except `SIMPLE_BOOTSTRAP=0` | | rc=1, fails again |

Working invocation (recovered from
`build/bootstrap/stage3/x86_64-pc-windows-msvc/stage2-command.transcript`):

```
SIMPLE_BOOTSTRAP=1 SIMPLE_NATIVE_BUILD_RUST=1 SIMPLE_LINKER_FLAVOR=msvc \
SIMPLE_WINDOWS_ABI=msvc SIMPLE_NO_STUB_FALLBACK=1 SIMPLE_NO_DEPRECATED_WARNINGS=1 \
RUST_LOG=error LIBRARY_PATH= \
  <compiler> native-build --target x86_64-pc-windows-msvc --backend llvm \
    --runtime-bundle core-c-bootstrap --runtime-path <stage2-runtime-authority> \
    --mode dynload h.spl -o h.exe
```

`SIMPLE_BOOTSTRAP` is the single discriminating knob; the flags alone are not
enough.

## Two distinct defects

1. **The diagnostic is unreadable.**
   `src/compiler/80.driver/driver_aot_native_output.spl:1526` returns
   `Err("AOT compile error in {name}: {err.to_text()}")`. `err.to_text()`
   renders `<invalid-heap:0x...>` — the Err payload is misdecoded, so the real
   backend error never reaches the user. Same class as the
   `phase 3 FAILED (diagnostics unreadable: error array did not survive
   transport)` transport corruption another session owns; NOT fixed here.

2. **The non-bootstrap AOT path is broken for a trivial program.**
   Under `SIMPLE_BOOTSTRAP=1`, `driver_aot_native_output.spl:1537-1540` copies
   `llvm_bootstrap_last_object_path()` instead of writing the backend's own
   object bytes. That branch works; the general branch does not. Whether the
   general path is "unsupported by design" for a bootstrap-stage binary is
   unknown — today it fails, and fails unreadably.

## Impact

Any agent probing `native-build` with a bare invocation concludes the compiler
is broken. The four caret-suite components were all measured this way. Also
means no `native-build` on this host is exercising the non-bootstrap object
path at all.

## Also observed

`native-build` of a minimal single-file generic fixture (`struct Box<T>` +
`impl Box<T>`) SEGVs (rc=139) after monomorphize, even with the working
invocation. See
`hir_generic_type_param_unresolved_cross_module_2026-09-03.md` § Related.
