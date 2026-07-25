# gdb_e2e.gdb — batch GDB session against OpenOCD :3333 over the GHDL
# remote_bitbang debug stack (see openocd_attach.md, gdb_e2e.md).
#
# Exercised through GDB's remote protocol (native RSP packets):
#   - attach          target extended-remote :3333 (OpenOCD halts the hart)
#   - GPR read        info registers -> abstract register reads ('g'/'p')
#   - GPR write       set $x5 = 0x123 -> abstract register write ('P'), read back
#   - memory read     x/4xw via SBA ('m'; sysbus is the only memory path)
#   - memory write    set {unsigned int} via SBA ('M'), read back
#   - pc write        set $pc = 0x100 -> abstract dpc write, read back
#   - continue/halt   continue & -> vCont;c, interrupt -> Ctrl-C, re-halt
#
# Exercised via the GDB monitor channel (qRcmd -> OpenOCD `step`):
#   - single step     dcsr.step + resumereq + re-halt; pc must be exactly +4.
#     NATIVE `stepi` IS BLOCKED ON HART INTEGRATION, not on tooling: GDB's
#     riscv stepping is breakpoint-based software single-step (riscv-tdep
#     plants a breakpoint at next-pc and resumes), which requires a hart
#     that actually fetches and executes from memory. The tb fake hart
#     (tb_openocd_bitbang.vhd) is a free-running pc model — it never
#     executes the planted breakpoint, so `stepi` would wait forever.
#     Additionally GDB's insn probe issues 16-bit reads, while this DM's
#     SBA advertises 32/64-bit only. Both resolve when a real rv32/rv64
#     hart with executable memory sits behind the DM.
#
# Machine-checkable markers (parsed by run_gdb_e2e.shs):
#   PC_ATTACH, X5_BEFORE/X5_AFTER, MEM28_AFTER, PC_BEFORE/PC_AFTER,
#   PC_HALTED, E2E_DONE

set pagination off
set confirm off
set architecture riscv:rv64
set remotetimeout 60

target extended-remote :3333

echo \n=== attach state ===\n
printf "PC_ATTACH=0x%lx\n", $pc

echo \n=== info registers (abstract GPR reads) ===\n
info registers

echo \n=== GPR write: set $x5 = 0x123 ===\n
printf "X5_BEFORE=0x%lx\n", $x5
set $x5 = 0x123
maintenance flush register-cache
printf "X5_AFTER=0x%lx\n", $x5
info registers t0

echo \n=== memory read via SBA: x/4xw 0x10 (sba_test_mem init pattern) ===\n
x/4xw 0x10

echo \n=== memory write via SBA: 0xfeedc0de -> 0x28, read back ===\n
set {unsigned int}0x28 = 0xfeedc0de
printf "MEM28_AFTER=0x%x\n", *(unsigned int*)0x28
x/1xw 0x28

echo \n=== pc write (abstract dpc write) + step via dcsr.step (expect pc+4) ===\n
set $pc = 0x100
maintenance flush register-cache
printf "PC_BEFORE=0x%lx\n", $pc
monitor step
maintenance flush register-cache
printf "PC_AFTER=0x%lx\n", $pc

# Native continue/halt: `continue` runs in the foreground (vCont;c); the
# harness watches for CONTINUE_STARTED in the log, then sends SIGINT to
# this gdb process — the interactive Ctrl-C path — which gdb forwards as
# the RSP 0x03 interrupt; OpenOCD raises haltreq and reports the stop.
# (A scripted `continue & ... interrupt` cannot work in -batch mode: the
# CLI event loop does not pump the async stop reply between script lines.)
echo \n=== continue (native vCont;c) then halt (Ctrl-C -> RSP 0x03, from harness) ===\n
echo CONTINUE_STARTED\n
continue
maintenance flush register-cache
printf "PC_HALTED=0x%lx\n", $pc

echo \n=== detach ===\n
detach
echo E2E_DONE\n
quit
