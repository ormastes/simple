# RISC-V FPGA Linux Hardware Status

Date: 2026-05-21

## Summary

The repository has an RV64/RISC-V FPGA Linux boot pipeline in source and tests, but Linux has not been demonstrated on a physical FPGA in this verification pass.

## What Was Verified

- Bounded `bin/simple test` runs for the RV64 feature specs passed without leaving `simple` child processes.
- Interpreter and native subprocess probes around the changed VHDL/RV64/RISC-V specs completed without new crashed runs.
- The historical crashed-run baseline remains 17 old May 20 zero-count runs.

## What Was Not Verified

- No real KV260/K26 FPGA was programmed.
- No Vivado bitstream generation/timing closure was run in this pass.
- No GHDL hardware simulation was run in this pass.
- No OpenSBI or Linux payload was loaded onto generated FPGA hardware.
- No UART/JTAG UART Linux boot log was observed from hardware.

## Answer

Can Simple RISC-V run Linux on FPGA?

- The codebase contains the intended RV64 FPGA Linux boot pipeline and tests for it.
- Current evidence proves source-level/test-runner readiness, not physical Linux boot.
- The answer becomes "yes, verified" only after GHDL/Vivado/hardware programming and UART boot-log evidence are captured.

Did this pass actually run Linux on FPGA?

- No. This pass did not run on physical FPGA hardware.
