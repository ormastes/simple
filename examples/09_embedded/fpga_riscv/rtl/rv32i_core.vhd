-- RV32I Single-Cycle CPU Core
-- Implements the full RV32I base integer instruction set
-- Target: ZedBoard Zynq-7020

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use work.rv32i_pkg.all;

entity rv32i_core is
    generic (
        RESET_ADDR : std_logic_vector(31 downto 0) := x"00000000"
    );
    port (
        clk       : in  std_logic;
        reset_n   : in  std_logic;
        -- Instruction memory interface
        imem_addr : out std_logic_vector(31 downto 0);
        imem_data : in  std_logic_vector(31 downto 0);
        -- Data memory interface
        dmem_addr  : out std_logic_vector(31 downto 0);
        dmem_wdata : out std_logic_vector(31 downto 0);
        dmem_rdata : in  std_logic_vector(31 downto 0);
        dmem_we    : out std_logic;
        dmem_re    : out std_logic;
        dmem_width : out std_logic_vector(1 downto 0);
        -- Status
        halted    : out std_logic
    );
end entity rv32i_core;

architecture rtl of rv32i_core is
    -- Program counter
    signal pc      : std_logic_vector(31 downto 0) := RESET_ADDR;
    signal pc_next : std_logic_vector(31 downto 0);
    signal pc_plus4 : std_logic_vector(31 downto 0);

    -- Decoder outputs
    signal opcode_w    : std_logic_vector(6 downto 0);
    signal rd_addr     : std_logic_vector(4 downto 0);
    signal rs1_addr    : std_logic_vector(4 downto 0);
    signal rs2_addr    : std_logic_vector(4 downto 0);
    signal funct3_w    : std_logic_vector(2 downto 0);
    signal funct7_w    : std_logic_vector(6 downto 0);
    signal imm_w       : std_logic_vector(31 downto 0);
    signal alu_op_w    : alu_op_t;
    signal reg_write_w : std_logic;
    signal mem_read_w  : std_logic;
    signal mem_write_w : std_logic;
    signal mem_to_reg_w : std_logic;
    signal alu_src_w   : std_logic;
    signal branch_w    : std_logic;
    signal jump_w      : std_logic;

    -- Register file
    signal rs1_data : std_logic_vector(31 downto 0);
    signal rs2_data : std_logic_vector(31 downto 0);
    signal rd_data  : std_logic_vector(31 downto 0);

    -- ALU
    signal alu_a      : std_logic_vector(31 downto 0);
    signal alu_b      : std_logic_vector(31 downto 0);
    signal alu_result : std_logic_vector(31 downto 0);
    signal alu_zero   : std_logic;

    -- Branch logic
    signal branch_taken : std_logic;
    signal branch_target : std_logic_vector(31 downto 0);

    -- Halt detection (ECALL/EBREAK)
    signal halt_r : std_logic := '0';

begin
    -- Instruction fetch
    imem_addr <= pc;
    pc_plus4  <= std_logic_vector(unsigned(pc) + 4);

    -- Decoder
    u_decoder : entity work.decoder
        port map (
            instruction => imem_data,
            opcode      => opcode_w,
            rd          => rd_addr,
            rs1         => rs1_addr,
            rs2         => rs2_addr,
            funct3      => funct3_w,
            funct7      => funct7_w,
            imm         => imm_w,
            alu_op      => alu_op_w,
            reg_write   => reg_write_w,
            mem_read    => mem_read_w,
            mem_write   => mem_write_w,
            mem_to_reg  => mem_to_reg_w,
            alu_src     => alu_src_w,
            branch      => branch_w,
            jump        => jump_w
        );

    -- Register file
    u_regfile : entity work.regfile
        port map (
            clk      => clk,
            rs1_addr => rs1_addr,
            rs2_addr => rs2_addr,
            rs1_data => rs1_data,
            rs2_data => rs2_data,
            rd_addr  => rd_addr,
            rd_data  => rd_data,
            rd_we    => reg_write_w
        );

    -- ALU source muxing
    alu_a <= pc when (opcode_w = OP_AUIPC or opcode_w = OP_JAL) else rs1_data;
    alu_b <= imm_w when alu_src_w = '1' else rs2_data;

    -- ALU
    u_alu : entity work.alu
        port map (
            op_a   => alu_a,
            op_b   => alu_b,
            alu_op => alu_op_w,
            result => alu_result,
            zero   => alu_zero
        );

    -- Branch evaluation
    process(branch_w, funct3_w, rs1_data, rs2_data)
    begin
        branch_taken <= '0';
        if branch_w = '1' then
            case funct3_w is
                when BR_BEQ  => if rs1_data = rs2_data then branch_taken <= '1'; end if;
                when BR_BNE  => if rs1_data /= rs2_data then branch_taken <= '1'; end if;
                when BR_BLT  => if signed(rs1_data) < signed(rs2_data) then branch_taken <= '1'; end if;
                when BR_BGE  => if signed(rs1_data) >= signed(rs2_data) then branch_taken <= '1'; end if;
                when BR_BLTU => if unsigned(rs1_data) < unsigned(rs2_data) then branch_taken <= '1'; end if;
                when BR_BGEU => if unsigned(rs1_data) >= unsigned(rs2_data) then branch_taken <= '1'; end if;
                when others  => branch_taken <= '0';
            end case;
        end if;
    end process;

    -- Branch/jump target
    branch_target <= std_logic_vector(unsigned(pc) + unsigned(imm_w));

    -- Next PC
    pc_next <= alu_result when opcode_w = OP_JALR else     -- JALR: rs1 + imm
               branch_target when (branch_taken = '1' or jump_w = '1') else
               pc_plus4;

    -- Register write-back mux
    rd_data <= dmem_rdata when mem_to_reg_w = '1' else
               pc_plus4 when jump_w = '1' else
               alu_result;

    -- Data memory interface
    dmem_addr  <= alu_result;
    dmem_wdata <= rs2_data;
    dmem_we    <= mem_write_w;
    dmem_re    <= mem_read_w;
    dmem_width <= funct3_w(1 downto 0);

    -- PC update + halt
    process(clk, reset_n)
    begin
        if reset_n = '0' then
            pc     <= RESET_ADDR;
            halt_r <= '0';
        elsif rising_edge(clk) then
            if halt_r = '0' then
                if opcode_w = OP_SYSTEM then
                    halt_r <= '1';  -- ECALL/EBREAK halts
                else
                    pc <= pc_next;
                end if;
            end if;
        end if;
    end process;

    halted <= halt_r;
end architecture rtl;
