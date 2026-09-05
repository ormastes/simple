# GHDL RV32 Mailbox Protocol

## Overview

The GHDL RV32 mailbox lane (`ghdl_rv32_mailbox`) provides a debugger-independent
simulation proof channel for bare-metal RISC-V programs running on the GHDL-simulated
RV32I CPU. Unlike the `ghdl_rv32_semihost` lane which relies on ARM semihosting trap
instruction sequences detected by the VHDL testbench, the mailbox lane uses pure
MMIO memory-mapped registers that the target writes to communicate with the host
simulation environment.

This makes the mailbox lane portable across any RISC-V simulator or FPGA fabric
that can map a memory region -- no debugger or special instruction detection is needed.

## Memory Map

RAM: 64 KB starting at `0x80000000` (addresses `0x80000000`--`0x8000FFFF`).

Mailbox registers are placed above the 64 KB RAM region to avoid address-space
collisions.

### Mailbox Register Block

**Base address:** `0x80FF0000`

| Offset | Name    | Direction     | Width  | Purpose                              |
|--------|---------|---------------|--------|--------------------------------------|
| +0x00  | CMD     | Target->Host  | 32-bit | Command code                         |
| +0x04  | ARG0    | Target->Host  | 32-bit | Argument / data pointer              |
| +0x08  | ARG1    | Target->Host  | 32-bit | Second argument                      |
| +0x0C  | STATUS  | Host->Target  | 32-bit | Response status (reserved)           |
| +0x10  | RESULT  | Host->Target  | 32-bit | Result value (reserved)              |
| +0x14  | SEQ_ID  | Target->Host  | 32-bit | Sequence counter (monotonic)         |
| +0x18  | TRIGGER | Target->Host  | 32-bit | Write `0x0000DEAD` to fire command   |

The register block spans 28 bytes (`0x80FF0000`--`0x80FF001B`).

### Sentinel Address

| Address      | Name          | Purpose                                    |
|-------------|---------------|--------------------------------------------|
| `0x80008000` | ram_sentinel  | Testbench writes final result here on exit |

## Commands

### CMD_PUTC (0x01)

Write one character to the simulation output stream.

- **CMD** = `0x01`
- **ARG0** = character value (low 8 bits used)
- **ARG1** = unused
- **Behavior:** Testbench appends `ARG0[7:0]` to an output buffer. Printable ASCII
  (32--126) and newline (10) are emitted; other values are silently dropped.

### CMD_EXIT (0x02)

Terminate simulation with an exit code.

- **CMD** = `0x02`
- **ARG0** = exit code (32-bit unsigned)
- **ARG1** = unused
- **Behavior:** Testbench writes the sentinel value `0xCAFE0000 | ARG0[15:0]` to
  RAM address `0x80008000`, then sets the `done` flag to halt the simulation.

### CMD_RESULT (0x03)

Report a structured test result without terminating.

- **CMD** = `0x03`
- **ARG0** = pass/fail (1 = pass, 0 = fail)
- **ARG1** = associated value (test-specific)
- **Behavior:** Testbench reports via VHDL `report` statement:
  `RESULT: pass=<ARG0> value=<ARG1>`.

## Protocol Sequence

1. Target writes `CMD`, `ARG0`, `ARG1` registers (order does not matter).
2. Target increments its local sequence counter and writes it to `SEQ_ID`.
3. Target writes `0x0000DEAD` to `TRIGGER`.
4. Testbench detects the trigger write on the next rising clock edge.
5. Testbench reads `CMD` and dispatches to the appropriate handler.
6. Testbench clears `TRIGGER` to `0x00000000` after processing.

## Sentinel Values

| Value               | Meaning                                |
|--------------------|----------------------------------------|
| `0xCAFE0000 | ec`  | Normal exit; low 16 bits = exit code   |
| `0xDEAD0000`       | Timeout -- simulation exceeded max cycles |

The runner script reads the sentinel word from simulation output to determine
the final exit code.

## Timeout

The testbench maintains a cycle counter. If it exceeds the configurable maximum
(default: 1,000,000 cycles), the testbench:

1. Writes `0xDEAD0000` to RAM address `0x80008000`.
2. Reports `SENTINEL: 0xDEAD0000`.
3. Sets `done` to halt the simulation.

## Reset

On simulation start (during reset), all mailbox register shadow variables in the
testbench are initialized to `0x00000000`.

## Comparison with Semihost Lane

| Aspect            | Semihost Lane              | Mailbox Lane               |
|-------------------|----------------------------|----------------------------|
| Detection method  | Instruction pattern match  | MMIO address decode        |
| Requires debugger | Conceptually yes           | No                         |
| Portability       | RISC-V semihost spec only  | Any memory-mapped target   |
| Complexity        | 3-instruction sequence     | Single store to TRIGGER    |
| Testbench entity  | `tb_semihost` / `tb_semi_run` | `tb_mailbox`           |
| Runner script     | `ghdl_runner.shs`          | `ghdl_mailbox_runner.shs`  |
