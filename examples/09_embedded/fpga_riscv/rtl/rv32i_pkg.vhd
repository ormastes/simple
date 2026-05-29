library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

package rv32i_pkg is
    constant OP_LUI    : std_logic_vector(6 downto 0) := "0110111";
    constant OP_AUIPC  : std_logic_vector(6 downto 0) := "0010111";
    constant OP_JAL    : std_logic_vector(6 downto 0) := "1101111";
    constant OP_JALR   : std_logic_vector(6 downto 0) := "1100111";
    constant OP_BRANCH : std_logic_vector(6 downto 0) := "1100011";
    constant OP_LOAD   : std_logic_vector(6 downto 0) := "0000011";
    constant OP_STORE  : std_logic_vector(6 downto 0) := "0100011";
    constant OP_IMMED  : std_logic_vector(6 downto 0) := "0010011";
    constant OP_REG    : std_logic_vector(6 downto 0) := "0110011";
    constant OP_SYSTEM : std_logic_vector(6 downto 0) := "1110011";

    type alu_op_t is (
        ALU_ADD, ALU_SUB, ALU_SLL, ALU_SLT, ALU_SLTU,
        ALU_XOR, ALU_SRL, ALU_SRA, ALU_OR, ALU_AND, ALU_PASS_B
    );

    constant BR_BEQ  : std_logic_vector(2 downto 0) := "000";
    constant BR_BNE  : std_logic_vector(2 downto 0) := "001";
    constant BR_BLT  : std_logic_vector(2 downto 0) := "100";
    constant BR_BGE  : std_logic_vector(2 downto 0) := "101";
    constant BR_BLTU : std_logic_vector(2 downto 0) := "110";
    constant BR_BGEU : std_logic_vector(2 downto 0) := "111";

    -- Semihosting magic instruction encodings
    constant SEMI_ENTRY : std_logic_vector(31 downto 0) := x"01f01013"; -- slli zero,zero,0x1f
    constant SEMI_BREAK : std_logic_vector(31 downto 0) := x"00100073"; -- ebreak
    constant SEMI_EXIT  : std_logic_vector(31 downto 0) := x"40705013"; -- srai zero,zero,0x7

    -- Semihosting operation codes
    constant SYS_WRITEC  : std_logic_vector(31 downto 0) := x"00000003";
    constant SYS_WRITE0  : std_logic_vector(31 downto 0) := x"00000004";
    constant SYS_EXIT    : std_logic_vector(31 downto 0) := x"00000018";

    -- Mailbox MMIO base address and register offsets
    constant MB_BASE_ADDR    : std_logic_vector(31 downto 0) := x"80FF0000";
    constant MB_OFF_CMD      : integer := 16#00#;
    constant MB_OFF_ARG0     : integer := 16#04#;
    constant MB_OFF_ARG1     : integer := 16#08#;
    constant MB_OFF_STATUS   : integer := 16#0C#;
    constant MB_OFF_RESULT   : integer := 16#10#;
    constant MB_OFF_SEQ_ID   : integer := 16#14#;
    constant MB_OFF_TRIGGER  : integer := 16#18#;

    -- Mailbox command codes
    constant MB_CMD_PUTC   : std_logic_vector(31 downto 0) := x"00000001";
    constant MB_CMD_EXIT   : std_logic_vector(31 downto 0) := x"00000002";
    constant MB_CMD_RESULT : std_logic_vector(31 downto 0) := x"00000003";

    -- Mailbox sentinel address (in RAM, word index = 0x8000/4 = 0x2000)
    constant MB_SENTINEL_ADDR : std_logic_vector(31 downto 0) := x"80008000";

    -- Mailbox sentinel value prefixes
    constant MB_SENTINEL_SUCCESS : std_logic_vector(31 downto 0) := x"CAFE0000";
    constant MB_SENTINEL_TIMEOUT : std_logic_vector(31 downto 0) := x"DEAD0000";

    -- Mailbox trigger magic value
    constant MB_TRIGGER_MAGIC : std_logic_vector(31 downto 0) := x"0000DEAD";
end package rv32i_pkg;
