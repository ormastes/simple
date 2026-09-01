# SimpleOS target codegen lacks `rt_struct_receiver_valid`

**Status:** Open — target-runtime defect; PID1 no longer depends on it

## Reproducer

```bash
bin/simple native-build --source src/compiler --source src/lib --source src/app --source src/os \
  --entry-closure --entry src/os/services/init/service_manager_main.spl \
  --target x86_64-unknown-simpleos --runtime-bundle simple-core --backend cranelift \
  -o build/os/rootfs/system/service_manager.smf
```

The native backend aborted in `rt_struct_receiver_valid` while compiling the
`ServiceWatch` receiver in `_poll_watch`. No output ELF was accepted or staged.

## Required resolution

Provide `rt_struct_receiver_valid` in the SimpleOS target runtime and add a
freestanding native smoke that performs a struct receiver field read. PID1 now
uses parallel primitive arrays and was linked successfully after the user
syscall trampoline was merged into its runtime archive; do not enable
`SIMPLE_ALLOW_STUB_FALLBACK` for this image.
