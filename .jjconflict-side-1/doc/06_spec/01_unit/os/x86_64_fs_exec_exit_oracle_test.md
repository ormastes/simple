# x86_64 Filesystem Execution Exit Oracle

Source: `test/01_unit/os/x86_64_fs_exec_exit_oracle_test.shs`

Evidence class: `source-contract` with a mutation check.

The shell test verifies that failure paths call the distinct failure exit,
success is emitted only after the final pass marker, and the runtime maps the
failure owner to a non-success ISA debug-exit value. It also mutates a temporary
copy to confirm the oracle detects a success call in the failure path.

This is static source-oracle evidence. It does not boot QEMU or observe an
actual emulator exit status.

