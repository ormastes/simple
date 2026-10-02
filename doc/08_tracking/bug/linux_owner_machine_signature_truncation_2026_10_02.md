# Linux owner text argument pairs truncated by runtime signature adaptation

The corrected native worker rejected parent acquisition with EINVAL before any
kernel call, despite a valid task/root request. GDB showed only two text values
at the four-machine-argument C entrypoint. Disassembly confirmed the generated
call set only rdi/rsi; rdx/rcx contained unrelated values. Native C tests passed
because they supplied the correct pointer/length pairs directly.

`text_arg_indices` entries alone were insufficient: missing `RuntimeFuncSpec`
declarations let Cranelift declare the Simple semantic arity and subsequently
truncate expanded pairs during signature adaptation. Register the exact machine
signatures for all eight Linux owner functions (2/4/1/5/18/1/1/1 parameters),
returning I64, in the Sys tier. Keep both the text expansion maps and machine
signature registry consistent with `runtime_linux_group_owner_impl.h`.

Regressions cover every machine signature, an actual generated Cranelift call
delivering four distinct words, and `linux_capacity_abi_main.spl`, which must be
compiled and run against the actual C adapter before worker qualification.
The C checks and admission limits are unchanged. Passing C-only tests or merely
building a worker image is not manager-task acceptance.

Evidence: capacity-sosix-cfe2287a-images-linux/gdb-copy-attempt1.log under the
manager bootstrap verification directory. The two original rejected manager
attempts remain preserved. Corrected producer/image qualification is pending.
