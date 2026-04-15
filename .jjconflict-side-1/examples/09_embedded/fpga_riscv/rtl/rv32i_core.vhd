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
        imem_addr : out std_logic_vector(31 downto 0);
        imem_data : in  std_logic_vector(31 downto 0);
        dmem_addr  : out std_logic_vector(31 downto 0);
        dmem_wdata : out std_logic_vector(31 downto 0);
        dmem_rdata : in  std_logic_vector(31 downto 0);
        dmem_we    : out std_logic;
        dmem_re    : out std_logic;
        dmem_width : out std_logic_vector(1 downto 0);
        halted     : out std_logic;
        -- Semihosting interface
        semi_trigger : out std_logic;
        semi_op      : out std_logic_vector(31 downto 0);
        semi_param   : out std_logic_vector(31 downto 0)
    );
end entity rv32i_core;

architecture rtl of rv32i_core is
    signal pc, pc_next, pc_plus4 : std_logic_vector(31 downto 0) := RESET_ADDR;
    signal opcode_w    : std_logic_vector(6 downto 0);
    signal rd_addr, rs1_addr, rs2_addr : std_logic_vector(4 downto 0);
    signal funct3_w    : std_logic_vector(2 downto 0);
    signal funct7_w    : std_logic_vector(6 downto 0);
    signal imm_w       : std_logic_vector(31 downto 0);
    signal alu_op_w    : alu_op_t;
    signal reg_write_w, mem_read_w, mem_write_w, mem_to_reg_w : std_logic;
    signal alu_src_w, branch_w, jump_w : std_logic;
    signal rs1_data, rs2_data, rd_data : std_logic_vector(31 downto 0);
    signal a0_val, a1_val : std_logic_vector(31 downto 0);
    signal alu_a, alu_b, alu_result : std_logic_vector(31 downto 0);
    signal alu_zero    : std_logic;
    signal branch_taken : std_logic;
    signal branch_target : std_logic_vector(31 downto 0);
    signal halt_r      : std_logic := '0';

    -- Semihosting detection: track 3-instruction magic sequence
    signal semi_phase  : integer range 0 to 3 := 0;
    signal semi_trig_r : std_logic := '0';
    signal semi_op_r   : std_logic_vector(31 downto 0) := (others => '0');
    signal semi_param_r : std_logic_vector(31 downto 0) := (others => '0');
    -- Suppress normal execution during semihost sequence
    signal semi_suppress : std_logic := '0';
begin
    imem_addr <= pc;
    pc_plus4  <= std_logic_vector(unsigned(pc) + 4);

    u_decoder : entity work.decoder
        port map (instruction=>imem_data, opcode=>opcode_w, rd=>rd_addr,
                  rs1=>rs1_addr, rs2=>rs2_addr, funct3=>funct3_w, funct7=>funct7_w,
                  imm=>imm_w, alu_op=>alu_op_w, reg_write=>reg_write_w,
                  mem_read=>mem_read_w, mem_write=>mem_write_w, mem_to_reg=>mem_to_reg_w,
                  alu_src=>alu_src_w, branch=>branch_w, jump=>jump_w);

    u_regfile : entity work.regfile
        port map (clk=>clk, rs1_addr=>rs1_addr, rs2_addr=>rs2_addr,
                  rs1_data=>rs1_data, rs2_data=>rs2_data,
                  rd_addr=>rd_addr, rd_data=>rd_data,
                  rd_we=>reg_write_w and (not semi_suppress),
                  a0_out=>a0_val, a1_out=>a1_val);

    alu_a <= pc when (opcode_w = OP_AUIPC or opcode_w = OP_JAL) else rs1_data;
    alu_b <= imm_w when alu_src_w = '1' else rs2_data;

    u_alu : entity work.alu
        port map (op_a=>alu_a, op_b=>alu_b, alu_op=>alu_op_w,
                  result=>alu_result, zero=>alu_zero);

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
                when others  => null;
            end case;
        end if;
    end process;

    branch_target <= std_logic_vector(unsigned(pc) + unsigned(imm_w));
    pc_next <= alu_result when opcode_w = OP_JALR else
               branch_target when (branch_taken = '1' or jump_w = '1') else
               pc_plus4;

    rd_data <= dmem_rdata when mem_to_reg_w = '1' else
               pc_plus4 when jump_w = '1' else
               alu_result;

    dmem_addr  <= alu_result;
    dmem_wdata <= rs2_data;
    dmem_we    <= mem_write_w and (not semi_suppress);
    dmem_re    <= mem_read_w;
    dmem_width <= funct3_w(1 downto 0);

    semi_trigger <= semi_trig_r;
    semi_op      <= semi_op_r;
    semi_param   <= semi_param_r;

    -- PC update + semihosting detection + halt
    process(clk, reset_n)
    begin
        if reset_n = '0' then
            pc <= RESET_ADDR;
            halt_r <= '0';
            semi_phase <= 0;
            semi_trig_r <= '0';
            semi_suppress <= '0';
        elsif rising_edge(clk) then
            semi_trig_r <= '0';  -- pulse

            if halt_r = '0' then
                -- Semihosting magic sequence detection
                if imem_data = SEMI_ENTRY and semi_phase = 0 then
                    -- Phase 1: slli zero,zero,0x1f detected
                    semi_phase <= 1;
                    pc <= pc_plus4;
                elsif imem_data = SEMI_BREAK and semi_phase = 1 then
                    -- Phase 2: ebreak detected after entry magic
                    semi_phase <= 2;
                    semi_op_r <= a0_val;
                    semi_param_r <= a1_val;
                    semi_suppress <= '1';
                    pc <= pc_plus4;
                elsif imem_data = SEMI_EXIT and semi_phase = 2 then
                    -- Phase 3: srai zero,zero,0x7 — trigger semihosting
                    semi_phase <= 0;
                    semi_trig_r <= '1';
                    semi_suppress <= '0';
                    -- Check for SYS_EXIT
                    if semi_op_r = SYS_EXIT then
                        halt_r <= '1';
                    else
                        pc <= pc_plus4;
                    end if;
                elsif opcode_w = OP_SYSTEM and semi_phase = 0 then
                    -- ecall/ebreak outside semihosting sequence = halt
                    halt_r <= '1';
                else
                    semi_phase <= 0;
                    semi_suppress <= '0';
                    pc <= pc_next;
                end if;
            end if;
        end if;
    end process;

    halted <= halt_r;
end architecture rtl;
