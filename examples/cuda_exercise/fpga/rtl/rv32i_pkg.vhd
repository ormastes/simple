-- RV32I Package - Shared types and constants
-- Target: ZedBoard Zynq-7020

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

package rv32i_pkg is
    -- Instruction opcodes
    constant OP_LUI    : std_logic_vector(6 downto 0) := "0110111";
    constant OP_AUIPC  : std_logic_vector(6 downto 0) := "0010111";
    constant OP_JAL    : std_logic_vector(6 downto 0) := "1101111";
    constant OP_JALR   : std_logic_vector(6 downto 0) := "1100111";
    constant OP_BRANCH : std_logic_vector(6 downto 0) := "1100011";
    constant OP_LOAD   : std_logic_vector(6 downto 0) := "0000011";
    constant OP_STORE  : std_logic_vector(6 downto 0) := "0100011";
    constant OP_IMMED  : std_logic_vector(6 downto 0) := "0010011";
    constant OP_REG    : std_logic_vector(6 downto 0) := "0110011";
    constant OP_FENCE  : std_logic_vector(6 downto 0) := "0001111";
    constant OP_SYSTEM : std_logic_vector(6 downto 0) := "1110011";

    -- ALU operations
    type alu_op_t is (
        ALU_ADD, ALU_SUB, ALU_SLL, ALU_SLT, ALU_SLTU,
        ALU_XOR, ALU_SRL, ALU_SRA, ALU_OR, ALU_AND,
        ALU_PASS_B  -- passthrough for LUI
    );

    -- Branch types
    constant BR_BEQ  : std_logic_vector(2 downto 0) := "000";
    constant BR_BNE  : std_logic_vector(2 downto 0) := "001";
    constant BR_BLT  : std_logic_vector(2 downto 0) := "100";
    constant BR_BGE  : std_logic_vector(2 downto 0) := "101";
    constant BR_BLTU : std_logic_vector(2 downto 0) := "110";
    constant BR_BGEU : std_logic_vector(2 downto 0) := "111";

    -- Memory access width
    type mem_width_t is (WIDTH_BYTE, WIDTH_HALF, WIDTH_WORD);

end package rv32i_pkg;
