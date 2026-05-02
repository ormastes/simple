-- generated-from: simple_rv32gc_core.spl
-- source-map: Rv32Instruction.opcode => imem_rdata(6 downto 0)
-- source-map: Rv32Instruction.rd => imem_rdata(11 downto 7)
-- source-map: Rv32Instruction.funct3 => imem_rdata(14 downto 12)
-- source-map: Rv32Instruction.rs1 => imem_rdata(19 downto 15)
-- source-map: Rv32Instruction.rs2 => imem_rdata(24 downto 20)
-- source-map: Rv32Instruction.funct7 => imem_rdata(31 downto 25)
-- source-map: RiscvBranchEncoding.bit11 => imem_rdata(7 downto 7)
-- source-map: RiscvBranchEncoding.low => imem_rdata(11 downto 8)
-- source-map: RiscvBranchEncoding.high => imem_rdata(30 downto 25)
-- source-map: RiscvBranchEncoding.bit12 => imem_rdata(31 downto 31)
-- source-map: RiscvStoreEncoding.low => imem_rdata(11 downto 7)
-- source-map: RiscvStoreEncoding.high => imem_rdata(31 downto 25)
-- source-map: RiscvIImmediateEncoding.value => imem_rdata(31 downto 20)
-- source-map: RiscvUpperImmediateEncoding.high20 => imem_rdata(31 downto 12)
-- source-map: RiscvExecuteControlEncoding.funct3 => imem_rdata(14 downto 12)
-- source-map: RiscvExecuteControlEncoding.shamt_low5 => imem_rdata(24 downto 20)
-- source-map: RiscvExecuteControlEncoding.shamt_bit5 => imem_rdata(25 downto 25)
-- source-map: RiscvExecuteControlEncoding.bit30 => imem_rdata(30 downto 30)
-- source-map: RiscvExecuteDatapathEncoding.opcode => imem_rdata(6 downto 0)
-- source-map: RiscvExecuteDatapathEncoding.funct3 => imem_rdata(14 downto 12)
-- source-map: RiscvExecuteDatapathEncoding.bit30 => imem_rdata(30 downto 30)
-- source-map: RiscvBranchDatapathEncoding.opcode => imem_rdata(6 downto 0)
-- source-map: RiscvBranchDatapathEncoding.funct3 => imem_rdata(14 downto 12)
-- source-map: RiscvControlFlowDatapathEncoding.opcode => imem_rdata(6 downto 0)
-- source-map: RiscvMemoryAccessControlEncoding.funct3 => imem_rdata(14 downto 12)
-- source-map: RiscvJumpEncoding.high8 => imem_rdata(19 downto 12)
-- source-map: RiscvJumpEncoding.bit11 => imem_rdata(20 downto 20)
-- source-map: RiscvJumpEncoding.low10 => imem_rdata(30 downto 21)
-- source-map: RiscvJumpEncoding.bit20 => imem_rdata(31 downto 31)
-- source-map: RiscvDispatchClassEncoding.opcode => imem_rdata(6 downto 0)
-- source-map: RiscvTrapHaltControlEncoding.opcode => imem_rdata(6 downto 0)
-- proof-lane: generated_rv32_baremetal shell=semihost+mailbox
-- readiness: contract linux-boot-validated=false

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

package simple_rv32i_core_pkg is
    constant XLEN : natural := 32;
    subtype xword_t is std_logic_vector(XLEN - 1 downto 0);
    constant RESET_VECTOR : xword_t := x"80000000";
    constant BOOT_STRIDE : natural := 4;
end package simple_rv32i_core_pkg;

package body simple_rv32i_core_pkg is
end package body simple_rv32i_core_pkg;
