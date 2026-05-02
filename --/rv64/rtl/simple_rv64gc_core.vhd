-- generated-from: simple_rv64gc_core.spl
-- source-map: Rv64Instruction.opcode => imem_rdata(6 downto 0)
-- source-map: Rv64Instruction.rd => imem_rdata(11 downto 7)
-- source-map: Rv64Instruction.funct3 => imem_rdata(14 downto 12)
-- source-map: Rv64Instruction.rs1 => imem_rdata(19 downto 15)
-- source-map: Rv64Instruction.rs2 => imem_rdata(24 downto 20)
-- source-map: Rv64Instruction.funct7 => imem_rdata(31 downto 25)
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
-- proof-lane: generated_rv64_linux shell=none
-- readiness: contract linux-boot-validated=false

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use work.simple_rv64i_core_pkg.all;

entity simple_rv64gc_core is
    port (
        clk           : in  std_logic;
        reset_n       : in  std_logic;
        imem_addr     : out xword_t;
        imem_rdata    : in  std_logic_vector(31 downto 0);
        dmem_addr     : out xword_t;
        dmem_wdata    : out xword_t;
        dmem_rdata    : in  xword_t;
        dmem_we       : out std_logic;
        dmem_re       : out std_logic;
        dmem_width    : out std_logic_vector(1 downto 0);
        dmem_wstrb    : out std_logic_vector((XLEN / 8) - 1 downto 0);
        debug_pc      : out xword_t;
        trap          : out std_logic;
        halt          : out std_logic
    );
end entity simple_rv64gc_core;

architecture rtl of simple_rv64gc_core is
    type reg_file_t is array (0 to 31) of xword_t;
    signal pc_reg : xword_t := RESET_VECTOR;
    signal regs : reg_file_t := (2 => x"0000000000000FFC", others => (others => '0'));
    signal dmem_addr_reg : xword_t := (others => '0');
    signal dmem_wdata_reg : xword_t := (others => '0');
    signal dmem_we_reg : std_logic := '0';
    signal dmem_re_reg : std_logic := '0';
    signal dmem_width_reg : std_logic_vector(1 downto 0) := "10";
    signal dmem_wstrb_reg : std_logic_vector((XLEN / 8) - 1 downto 0) := (others => '0');
    signal trap_reg : std_logic := '0';
    signal halt_reg : std_logic := '0';
begin
    imem_addr <= pc_reg;
    dmem_addr <= dmem_addr_reg;
    dmem_wdata <= dmem_wdata_reg;
    dmem_we <= dmem_we_reg;
    dmem_re <= dmem_re_reg;
    dmem_width <= dmem_width_reg;
    dmem_wstrb <= dmem_wstrb_reg;
    debug_pc <= pc_reg;
    trap <= trap_reg;
    halt <= halt_reg;

    process(clk, reset_n)
        variable rd_i : integer range 0 to 31;
        variable rs1_i : integer range 0 to 31;
        variable rs2_i : integer range 0 to 31;
        variable imm_i : signed(XLEN - 1 downto 0);
        variable addr_i : unsigned(XLEN - 1 downto 0);
        variable branch_i : signed(XLEN - 1 downto 0);
        variable jump_i : signed(XLEN - 1 downto 0);
        variable imm_u : xword_t;
        variable decode_writeback_bits : std_logic_vector(31 downto 0);
        variable decode_branch_immediate_bits : std_logic_vector(31 downto 0);
        variable decode_store_immediate_bits : std_logic_vector(31 downto 0);
        variable decode_i_immediate_bits : std_logic_vector(31 downto 0);
        variable decode_upper_immediate_bits : std_logic_vector(31 downto 0);
        variable decode_execute_control_bits : std_logic_vector(31 downto 0);
        variable decode_execute_datapath_bits : std_logic_vector(31 downto 0);
        variable decode_branch_datapath_bits : std_logic_vector(31 downto 0);
        variable decode_control_flow_datapath_bits : std_logic_vector(31 downto 0);
        variable decode_memory_access_control_bits : std_logic_vector(31 downto 0);
        variable decode_jump_immediate_bits : std_logic_vector(31 downto 0);
        variable decode_dispatch_class_bits : std_logic_vector(31 downto 0);
        variable decode_trap_halt_control_bits : std_logic_vector(31 downto 0);
        variable decode_writeback_rd_i : integer range 0 to 31;
        variable branch_taken : boolean;
        variable shift_i : natural range 0 to 63;
        variable decode_execute_alu_op : std_logic_vector(3 downto 0);
        variable decode_execute_is_reg : std_logic;
        variable decode_branch_op : std_logic_vector(2 downto 0);
        variable decode_next_pc_op : std_logic_vector(1 downto 0);
        variable decode_writes_link : std_logic;
        variable decode_memory_funct3 : std_logic_vector(2 downto 0);
        variable decode_dispatch_class : std_logic_vector(3 downto 0);
        variable decode_continue_exec : std_logic;
        variable decode_should_trap : std_logic;
        variable decode_should_halt : std_logic;
    begin
        if reset_n = '0' then
            pc_reg <= RESET_VECTOR;
            regs <= (2 => x"0000000000000FFC", others => (others => '0'));
            dmem_addr_reg <= (others => '0');
            dmem_wdata_reg <= (others => '0');
            dmem_we_reg <= '0';
            dmem_re_reg <= '0';
            dmem_width_reg <= "10";
            dmem_wstrb_reg <= (others => '0');
            trap_reg <= '0';
            halt_reg <= '0';
        elsif rising_edge(clk) then
            dmem_we_reg <= '0';
            dmem_re_reg <= '0';
            dmem_width_reg <= "10";
            dmem_wstrb_reg <= (others => '0');
            if halt_reg = '0' and trap_reg = '0' then
                rd_i := to_integer(unsigned(imem_rdata(11 downto 7)));
                rs1_i := to_integer(unsigned(imem_rdata(19 downto 15)));
                rs2_i := to_integer(unsigned(imem_rdata(24 downto 20)));
                decode_writeback_bits := imem_rdata;
                decode_branch_immediate_bits := (others => '0');
                decode_store_immediate_bits := (others => '0');
                decode_i_immediate_bits := (others => '0');
                decode_upper_immediate_bits := (others => '0');
                decode_execute_control_bits := (others => '0');
                decode_execute_datapath_bits := (others => '0');
                decode_branch_datapath_bits := (others => '0');
                decode_control_flow_datapath_bits := (others => '0');
                decode_memory_access_control_bits := (others => '0');
                decode_jump_immediate_bits := (others => '0');
                decode_dispatch_class_bits := (others => '0');
                decode_trap_halt_control_bits := (others => '0');
                if imem_rdata(6 downto 0) = "0110111" then
                    decode_dispatch_class_bits := "0000000000000000000000000000" & "0001";
                    decode_trap_halt_control_bits := "00000000000000000000000000000" & '0' & '0' & '1';
                elsif imem_rdata(6 downto 0) = "0010111" then
                    decode_dispatch_class_bits := "0000000000000000000000000000" & "0010";
                    decode_trap_halt_control_bits := "00000000000000000000000000000" & '0' & '0' & '1';
                elsif imem_rdata(6 downto 0) = "0010011" then
                    decode_dispatch_class_bits := "0000000000000000000000000000" & "0011";
                    decode_trap_halt_control_bits := "00000000000000000000000000000" & '0' & '0' & '1';
                elsif imem_rdata(6 downto 0) = "0110011" then
                    decode_dispatch_class_bits := "0000000000000000000000000000" & "0100";
                    decode_trap_halt_control_bits := "00000000000000000000000000000" & '0' & '0' & '1';
                elsif imem_rdata(6 downto 0) = "0000011" then
                    decode_dispatch_class_bits := "0000000000000000000000000000" & "0101";
                    decode_trap_halt_control_bits := "00000000000000000000000000000" & '0' & '0' & '1';
                elsif imem_rdata(6 downto 0) = "0100011" then
                    decode_dispatch_class_bits := "0000000000000000000000000000" & "0110";
                    decode_trap_halt_control_bits := "00000000000000000000000000000" & '0' & '0' & '1';
                elsif imem_rdata(6 downto 0) = "1100011" then
                    decode_dispatch_class_bits := "0000000000000000000000000000" & "0111";
                    decode_trap_halt_control_bits := "00000000000000000000000000000" & '0' & '0' & '1';
                elsif imem_rdata(6 downto 0) = "1100111" then
                    decode_dispatch_class_bits := "0000000000000000000000000000" & "1000";
                    decode_trap_halt_control_bits := "00000000000000000000000000000" & '0' & '0' & '1';
                elsif imem_rdata(6 downto 0) = "1101111" then
                    decode_dispatch_class_bits := "0000000000000000000000000000" & "1001";
                    decode_trap_halt_control_bits := "00000000000000000000000000000" & '0' & '0' & '1';
                elsif imem_rdata(6 downto 0) = "0001111" then
                    decode_dispatch_class_bits := "0000000000000000000000000000" & "1010";
                    decode_trap_halt_control_bits := "00000000000000000000000000000" & '0' & '0' & '1';
                elsif imem_rdata(6 downto 0) = "1110011" then
                    decode_dispatch_class_bits := "0000000000000000000000000000" & "1011";
                    decode_trap_halt_control_bits := "00000000000000000000000000000" & '1' & '0' & '0';
                else
                    decode_trap_halt_control_bits := "00000000000000000000000000000" & '0' & '1' & '0';
                end if;
                case decode_dispatch_class_bits(3 downto 0) is
                    when "0001" | "0010" =>
                        decode_upper_immediate_bits := imem_rdata(31 downto 12) & "000000000000";
                    when "0011" =>
                        decode_writeback_bits := imem_rdata(31 downto 12) & imem_rdata(19 downto 15) & imem_rdata(6 downto 0);
                        decode_i_immediate_bits := "00000000000000000000" & imem_rdata(31 downto 20);
                        decode_execute_control_bits := "0000000000000000000000" & imem_rdata(25 downto 25) & imem_rdata(30 downto 30) & imem_rdata(14 downto 12);
                        if imem_rdata(14 downto 12) = "000" then
                            decode_execute_datapath_bits := "00000000000000000000000000000" & "0000" & '0';
                        elsif imem_rdata(14 downto 12) = "001" then
                            decode_execute_datapath_bits := "00000000000000000000000000000" & "0010" & '0';
                        elsif imem_rdata(14 downto 12) = "010" then
                            decode_execute_datapath_bits := "00000000000000000000000000000" & "0011" & '0';
                        elsif imem_rdata(14 downto 12) = "011" then
                            decode_execute_datapath_bits := "00000000000000000000000000000" & "0100" & '0';
                        elsif imem_rdata(14 downto 12) = "100" then
                            decode_execute_datapath_bits := "00000000000000000000000000000" & "0101" & '0';
                        elsif imem_rdata(14 downto 12) = "101" and imem_rdata(30 downto 30) = "0" then
                            decode_execute_datapath_bits := "00000000000000000000000000000" & "0110" & '0';
                        elsif imem_rdata(14 downto 12) = "101" and imem_rdata(30 downto 30) = "1" then
                            decode_execute_datapath_bits := "00000000000000000000000000000" & "0111" & '0';
                        elsif imem_rdata(14 downto 12) = "110" then
                            decode_execute_datapath_bits := "00000000000000000000000000000" & "1000" & '0';
                        elsif imem_rdata(14 downto 12) = "111" then
                            decode_execute_datapath_bits := "00000000000000000000000000000" & "1001" & '0';
                        end if;
                    when "0100" =>
                        decode_execute_control_bits := "0000000000000000000000" & imem_rdata(25 downto 25) & imem_rdata(30 downto 30) & imem_rdata(14 downto 12);
                        if imem_rdata(14 downto 12) = "000" and imem_rdata(31 downto 25) = "0000000" then
                            decode_writeback_bits := imem_rdata(31 downto 12) & imem_rdata(24 downto 20) & imem_rdata(6 downto 0);
                        end if;
                        if imem_rdata(14 downto 12) = "000" and imem_rdata(30 downto 30) = "0" then
                            decode_execute_datapath_bits := "00000000000000000000000000000" & "0000" & '1';
                        elsif imem_rdata(14 downto 12) = "000" and imem_rdata(30 downto 30) = "1" then
                            decode_execute_datapath_bits := "00000000000000000000000000000" & "0001" & '1';
                        elsif imem_rdata(14 downto 12) = "001" then
                            decode_execute_datapath_bits := "00000000000000000000000000000" & "0010" & '1';
                        elsif imem_rdata(14 downto 12) = "010" then
                            decode_execute_datapath_bits := "00000000000000000000000000000" & "0011" & '1';
                        elsif imem_rdata(14 downto 12) = "011" then
                            decode_execute_datapath_bits := "00000000000000000000000000000" & "0100" & '1';
                        elsif imem_rdata(14 downto 12) = "100" then
                            decode_execute_datapath_bits := "00000000000000000000000000000" & "0101" & '1';
                        elsif imem_rdata(14 downto 12) = "101" and imem_rdata(30 downto 30) = "0" then
                            decode_execute_datapath_bits := "00000000000000000000000000000" & "0110" & '1';
                        elsif imem_rdata(14 downto 12) = "101" and imem_rdata(30 downto 30) = "1" then
                            decode_execute_datapath_bits := "00000000000000000000000000000" & "0111" & '1';
                        elsif imem_rdata(14 downto 12) = "110" then
                            decode_execute_datapath_bits := "00000000000000000000000000000" & "1000" & '1';
                        elsif imem_rdata(14 downto 12) = "111" then
                            decode_execute_datapath_bits := "00000000000000000000000000000" & "1001" & '1';
                        end if;
                    when "0101" =>
                        decode_i_immediate_bits := "00000000000000000000" & imem_rdata(31 downto 20);
                        decode_memory_access_control_bits := "00000000000000000000000000000" & imem_rdata(14 downto 12);
                    when "0110" =>
                        decode_store_immediate_bits := "00000000000000000000" & imem_rdata(31 downto 25) & imem_rdata(11 downto 7);
                        decode_memory_access_control_bits := "00000000000000000000000000000" & imem_rdata(14 downto 12);
                    when "0111" =>
                        decode_branch_immediate_bits := "00000000000000000000" & imem_rdata(31 downto 31) & imem_rdata(7 downto 7) & imem_rdata(30 downto 25) & imem_rdata(11 downto 8);
                        decode_execute_control_bits := "0000000000000000000000" & imem_rdata(25 downto 25) & imem_rdata(30 downto 30) & imem_rdata(14 downto 12);
                        if imem_rdata(14 downto 12) = "000" then
                            decode_branch_datapath_bits := "00000000000000000000000000000" & "000";
                        elsif imem_rdata(14 downto 12) = "001" then
                            decode_branch_datapath_bits := "00000000000000000000000000000" & "001";
                        elsif imem_rdata(14 downto 12) = "100" then
                            decode_branch_datapath_bits := "00000000000000000000000000000" & "010";
                        elsif imem_rdata(14 downto 12) = "101" then
                            decode_branch_datapath_bits := "00000000000000000000000000000" & "011";
                        elsif imem_rdata(14 downto 12) = "110" then
                            decode_branch_datapath_bits := "00000000000000000000000000000" & "100";
                        elsif imem_rdata(14 downto 12) = "111" then
                            decode_branch_datapath_bits := "00000000000000000000000000000" & "101";
                        end if;
                        decode_control_flow_datapath_bits := "00000000000000000000000000000" & '0' & "01";
                    when "1000" =>
                        decode_control_flow_datapath_bits := "00000000000000000000000000000" & '1' & "10";
                    when "1001" =>
                        decode_jump_immediate_bits := "000000000000" & imem_rdata(31 downto 31) & imem_rdata(19 downto 12) & imem_rdata(20 downto 20) & imem_rdata(30 downto 21);
                        decode_control_flow_datapath_bits := "00000000000000000000000000000" & '1' & "11";
                    when others => null;
                end case;
                decode_writeback_rd_i := to_integer(unsigned(decode_writeback_bits(11 downto 7)));
                imm_i := resize(signed(decode_i_immediate_bits(11 downto 0)), XLEN);
                imm_u := std_logic_vector(resize(signed(decode_upper_immediate_bits(31 downto 12) & "000000000000"), XLEN));
                branch_i := resize(signed(decode_branch_immediate_bits(11) & decode_branch_immediate_bits(10) & decode_branch_immediate_bits(9 downto 4) & decode_branch_immediate_bits(3 downto 0) & '0'), XLEN);
                jump_i := resize(signed(decode_jump_immediate_bits(19) & decode_jump_immediate_bits(18 downto 11) & decode_jump_immediate_bits(10) & decode_jump_immediate_bits(9 downto 0) & '0'), XLEN);
                branch_taken := false;
                shift_i := to_integer(unsigned(regs(rs2_i)(5 downto 0)));
                decode_execute_alu_op := decode_execute_datapath_bits(4 downto 1);
                decode_execute_is_reg := decode_execute_datapath_bits(0);
                decode_branch_op := decode_branch_datapath_bits(2 downto 0);
                decode_next_pc_op := decode_control_flow_datapath_bits(1 downto 0);
                decode_writes_link := decode_control_flow_datapath_bits(2);
                decode_memory_funct3 := decode_memory_access_control_bits(2 downto 0);
                decode_dispatch_class := decode_dispatch_class_bits(3 downto 0);
                decode_continue_exec := decode_trap_halt_control_bits(0);
                decode_should_trap := decode_trap_halt_control_bits(1);
                decode_should_halt := decode_trap_halt_control_bits(2);
                if decode_continue_exec = '1' then
                        case decode_dispatch_class is
                            when "0001" =>
                                if rd_i /= 0 then
                                    regs(rd_i) <= imm_u;
                                end if;
                                pc_reg <= std_logic_vector(unsigned(pc_reg) + to_unsigned(BOOT_STRIDE, XLEN));
                            when "0010" =>
                                if rd_i /= 0 then
                                    regs(rd_i) <= std_logic_vector(signed(pc_reg) + signed(imm_u));
                                end if;
                                pc_reg <= std_logic_vector(unsigned(pc_reg) + to_unsigned(BOOT_STRIDE, XLEN));
                            when "0011" =>
                                if decode_writeback_rd_i /= 0 then
                                    if decode_execute_is_reg = '0' then
                                        case decode_execute_alu_op is
                                            when "0000" => regs(decode_writeback_rd_i) <= std_logic_vector(signed(regs(rs1_i)) + imm_i);
                                            when "0011" =>
                                                if signed(regs(rs1_i)) < imm_i then
                                                    regs(decode_writeback_rd_i) <= std_logic_vector(to_unsigned(1, XLEN));
                                                else
                                                    regs(decode_writeback_rd_i) <= (others => '0');
                                                end if;
                                            when "0100" =>
                                                if unsigned(regs(rs1_i)) < unsigned(std_logic_vector(imm_i)) then
                                                    regs(decode_writeback_rd_i) <= std_logic_vector(to_unsigned(1, XLEN));
                                                else
                                                    regs(decode_writeback_rd_i) <= (others => '0');
                                                end if;
                                            when "0101" => regs(decode_writeback_rd_i) <= regs(rs1_i) xor std_logic_vector(imm_i);
                                            when "1000" => regs(decode_writeback_rd_i) <= regs(rs1_i) or std_logic_vector(imm_i);
                                            when "1001" => regs(decode_writeback_rd_i) <= regs(rs1_i) and std_logic_vector(imm_i);
                                            when "0010" => regs(decode_writeback_rd_i) <= std_logic_vector(shift_left(unsigned(regs(rs1_i)), to_integer(unsigned(decode_execute_control_bits(9 downto 4)))));
                                            when "0110" => regs(decode_writeback_rd_i) <= std_logic_vector(shift_right(unsigned(regs(rs1_i)), to_integer(unsigned(decode_execute_control_bits(9 downto 4)))));
                                            when "0111" => regs(decode_writeback_rd_i) <= std_logic_vector(shift_right(signed(regs(rs1_i)), to_integer(unsigned(decode_execute_control_bits(9 downto 4)))));
                                            when others => trap_reg <= '1';
                                        end case;
                                    else
                                        trap_reg <= '1';
                                    end if;
                                end if;
                                pc_reg <= std_logic_vector(unsigned(pc_reg) + to_unsigned(BOOT_STRIDE, XLEN));
                            when "0100" =>
                                if decode_writeback_rd_i /= 0 then
                                    if decode_execute_is_reg = '1' then
                                        case decode_execute_alu_op is
                                            when "0000" => regs(decode_writeback_rd_i) <= std_logic_vector(signed(regs(rs1_i)) + signed(regs(rs2_i)));
                                            when "0001" => regs(decode_writeback_rd_i) <= std_logic_vector(signed(regs(rs1_i)) - signed(regs(rs2_i)));
                                            when "0010" => regs(decode_writeback_rd_i) <= std_logic_vector(shift_left(unsigned(regs(rs1_i)), shift_i));
                                            when "0011" =>
                                                if signed(regs(rs1_i)) < signed(regs(rs2_i)) then
                                                    regs(decode_writeback_rd_i) <= std_logic_vector(to_unsigned(1, XLEN));
                                                else
                                                    regs(decode_writeback_rd_i) <= (others => '0');
                                                end if;
                                            when "0100" =>
                                                if unsigned(regs(rs1_i)) < unsigned(regs(rs2_i)) then
                                                    regs(decode_writeback_rd_i) <= std_logic_vector(to_unsigned(1, XLEN));
                                                else
                                                    regs(decode_writeback_rd_i) <= (others => '0');
                                                end if;
                                            when "0101" => regs(decode_writeback_rd_i) <= regs(rs1_i) xor regs(rs2_i);
                                            when "0110" => regs(decode_writeback_rd_i) <= std_logic_vector(shift_right(unsigned(regs(rs1_i)), shift_i));
                                            when "0111" => regs(decode_writeback_rd_i) <= std_logic_vector(shift_right(signed(regs(rs1_i)), shift_i));
                                            when "1000" => regs(decode_writeback_rd_i) <= regs(rs1_i) or regs(rs2_i);
                                            when "1001" => regs(decode_writeback_rd_i) <= regs(rs1_i) and regs(rs2_i);
                                            when others => trap_reg <= '1';
                                        end case;
                                    else
                                        trap_reg <= '1';
                                    end if;
                                end if;
                                pc_reg <= std_logic_vector(unsigned(pc_reg) + to_unsigned(BOOT_STRIDE, XLEN));
                            when "0101" =>
                                addr_i := unsigned(signed(regs(rs1_i)) + imm_i);
                                dmem_addr_reg <= std_logic_vector(addr_i);
                                dmem_re_reg <= '1';
                                case decode_memory_funct3 is
                                    when "000" =>
                                        dmem_width_reg <= "00";
                                        if XLEN = 64 then
                                            if rd_i /= 0 then
                                                regs(rd_i) <= std_logic_vector(resize(signed(std_logic_vector(shift_right(unsigned(dmem_rdata), to_integer(unsigned(addr_i(2 downto 0))) * 8))(7 downto 0)), XLEN));
                                            end if;
                                        elif rd_i /= 0 then
                                            regs(rd_i) <= std_logic_vector(resize(signed(std_logic_vector(shift_right(unsigned(dmem_rdata), to_integer(unsigned(addr_i(1 downto 0))) * 8))(7 downto 0)), XLEN));
                                        end if;
                                    when "001" =>
                                        dmem_width_reg <= "01";
                                        if addr_i(0) = '1' then
                                            trap_reg <= '1';
                                        elif XLEN = 64 then
                                            if rd_i /= 0 then
                                                regs(rd_i) <= std_logic_vector(resize(signed(std_logic_vector(shift_right(unsigned(dmem_rdata), to_integer(unsigned(addr_i(2 downto 0))) * 8))(15 downto 0)), XLEN));
                                            end if;
                                        elif rd_i /= 0 then
                                            regs(rd_i) <= std_logic_vector(resize(signed(std_logic_vector(shift_right(unsigned(dmem_rdata), to_integer(unsigned(addr_i(1 downto 0))) * 8))(15 downto 0)), XLEN));
                                        end if;
                                    when "010" =>
                                        dmem_width_reg <= "10";
                                        if addr_i(1 downto 0) /= "00" then
                                            trap_reg <= '1';
                                        elif XLEN = 64 then
                                            if rd_i /= 0 then
                                                regs(rd_i) <= std_logic_vector(resize(signed(std_logic_vector(shift_right(unsigned(dmem_rdata), to_integer(unsigned(addr_i(2 downto 0))) * 8))(31 downto 0)), XLEN));
                                            end if;
                                        elif rd_i /= 0 then
                                            regs(rd_i) <= std_logic_vector(resize(signed(dmem_rdata(31 downto 0)), XLEN));
                                        end if;
                                    when "011" =>
                                        dmem_width_reg <= "11";
                                        if XLEN = 64 then
                                            if addr_i(2 downto 0) /= "000" then
                                                trap_reg <= '1';
                                            elif rd_i /= 0 then
                                                regs(rd_i) <= dmem_rdata;
                                            end if;
                                        else
                                            trap_reg <= '1';
                                        end if;
                                    when "100" =>
                                        dmem_width_reg <= "00";
                                        if XLEN = 64 then
                                            if rd_i /= 0 then
                                                regs(rd_i) <= std_logic_vector(resize(unsigned(std_logic_vector(shift_right(unsigned(dmem_rdata), to_integer(unsigned(addr_i(2 downto 0))) * 8))(7 downto 0)), XLEN));
                                            end if;
                                        elif rd_i /= 0 then
                                            regs(rd_i) <= std_logic_vector(resize(unsigned(std_logic_vector(shift_right(unsigned(dmem_rdata), to_integer(unsigned(addr_i(1 downto 0))) * 8))(7 downto 0)), XLEN));
                                        end if;
                                    when "101" =>
                                        dmem_width_reg <= "01";
                                        if addr_i(0) = '1' then
                                            trap_reg <= '1';
                                        elif XLEN = 64 then
                                            if rd_i /= 0 then
                                                regs(rd_i) <= std_logic_vector(resize(unsigned(std_logic_vector(shift_right(unsigned(dmem_rdata), to_integer(unsigned(addr_i(2 downto 0))) * 8))(15 downto 0)), XLEN));
                                            end if;
                                        elif rd_i /= 0 then
                                            regs(rd_i) <= std_logic_vector(resize(unsigned(std_logic_vector(shift_right(unsigned(dmem_rdata), to_integer(unsigned(addr_i(1 downto 0))) * 8))(15 downto 0)), XLEN));
                                        end if;
                                    when "110" =>
                                        dmem_width_reg <= "10";
                                        if XLEN = 64 then
                                            if addr_i(1 downto 0) /= "00" then
                                                trap_reg <= '1';
                                            elif rd_i /= 0 then
                                                regs(rd_i) <= std_logic_vector(resize(unsigned(std_logic_vector(shift_right(unsigned(dmem_rdata), to_integer(unsigned(addr_i(2 downto 0))) * 8))(31 downto 0)), XLEN));
                                            end if;
                                        else
                                            trap_reg <= '1';
                                        end if;
                                    when others => trap_reg <= '1';
                                end case;
                                pc_reg <= std_logic_vector(unsigned(pc_reg) + to_unsigned(BOOT_STRIDE, XLEN));
                            when "0110" =>
                                imm_i := resize(signed(decode_store_immediate_bits(11 downto 5) & decode_store_immediate_bits(4 downto 0)), XLEN);
                                addr_i := unsigned(signed(regs(rs1_i)) + imm_i);
                                dmem_addr_reg <= std_logic_vector(addr_i);
                                case decode_memory_funct3 is
                                    when "000" =>
                                        dmem_width_reg <= "00";
                                        if XLEN = 64 then
                                            dmem_wdata_reg <= std_logic_vector(shift_left(unsigned(regs(rs2_i)), to_integer(unsigned(addr_i(2 downto 0))) * 8));
                                            dmem_wstrb_reg <= std_logic_vector(shift_left(to_unsigned(1, XLEN / 8), to_integer(unsigned(addr_i(2 downto 0)))));
                                        else
                                            dmem_wdata_reg <= std_logic_vector(shift_left(unsigned(regs(rs2_i)), to_integer(unsigned(addr_i(1 downto 0))) * 8));
                                            dmem_wstrb_reg <= std_logic_vector(shift_left(to_unsigned(1, XLEN / 8), to_integer(unsigned(addr_i(1 downto 0)))));
                                        end if;
                                        dmem_we_reg <= '1';
                                    when "001" =>
                                        dmem_width_reg <= "01";
                                        if addr_i(0) = '1' then
                                            trap_reg <= '1';
                                        elif XLEN = 64 then
                                            dmem_wdata_reg <= std_logic_vector(shift_left(unsigned(regs(rs2_i)), to_integer(unsigned(addr_i(2 downto 0))) * 8));
                                            dmem_wstrb_reg <= std_logic_vector(shift_left(to_unsigned(3, XLEN / 8), to_integer(unsigned(addr_i(2 downto 0)))));
                                            dmem_we_reg <= '1';
                                        else
                                            dmem_wdata_reg <= std_logic_vector(shift_left(unsigned(regs(rs2_i)), to_integer(unsigned(addr_i(1 downto 0))) * 8));
                                            dmem_wstrb_reg <= std_logic_vector(shift_left(to_unsigned(3, XLEN / 8), to_integer(unsigned(addr_i(1 downto 0)))));
                                            dmem_we_reg <= '1';
                                        end if;
                                    when "010" =>
                                        dmem_width_reg <= "10";
                                        if addr_i(1 downto 0) /= "00" then
                                            trap_reg <= '1';
                                        elif XLEN = 64 then
                                            dmem_wdata_reg <= std_logic_vector(shift_left(unsigned(regs(rs2_i)), to_integer(unsigned(addr_i(2 downto 0))) * 8));
                                            dmem_wstrb_reg <= std_logic_vector(shift_left(to_unsigned(15, XLEN / 8), to_integer(unsigned(addr_i(2 downto 0)))));
                                            dmem_we_reg <= '1';
                                        elif XLEN = 32 then
                                            dmem_wdata_reg <= regs(rs2_i);
                                            dmem_wstrb_reg <= std_logic_vector(to_unsigned(15, XLEN / 8));
                                            dmem_we_reg <= '1';
                                        else
                                            trap_reg <= '1';
                                        end if;
                                    when "011" =>
                                        dmem_width_reg <= "11";
                                        if XLEN = 64 then
                                            if addr_i(2 downto 0) /= "000" then
                                                trap_reg <= '1';
                                            else
                                                dmem_wdata_reg <= regs(rs2_i);
                                                dmem_wstrb_reg <= (others => '1');
                                                dmem_we_reg <= '1';
                                            end if;
                                        else
                                            trap_reg <= '1';
                                        end if;
                                    when others =>
                                        dmem_width_reg <= "00";
                                        trap_reg <= '1';
                                end case;
                                pc_reg <= std_logic_vector(unsigned(pc_reg) + to_unsigned(BOOT_STRIDE, XLEN));
                            when "0111" =>
                                case decode_branch_op is
                                    when "000" => branch_taken := regs(rs1_i) = regs(rs2_i);
                                    when "001" => branch_taken := regs(rs1_i) /= regs(rs2_i);
                                    when "010" => branch_taken := signed(regs(rs1_i)) < signed(regs(rs2_i));
                                    when "011" => branch_taken := signed(regs(rs1_i)) >= signed(regs(rs2_i));
                                    when "100" => branch_taken := unsigned(regs(rs1_i)) < unsigned(regs(rs2_i));
                                    when "101" => branch_taken := unsigned(regs(rs1_i)) >= unsigned(regs(rs2_i));
                                    when others => trap_reg <= '1';
                                end case;
                                if decode_next_pc_op = "01" and branch_taken then
                                    pc_reg <= std_logic_vector(unsigned(signed(pc_reg) + branch_i));
                                else
                                    pc_reg <= std_logic_vector(unsigned(pc_reg) + to_unsigned(BOOT_STRIDE, XLEN));
                                end if;
                            when "1000" =>
                                if decode_writes_link = '1' and rd_i /= 0 then
                                    regs(rd_i) <= std_logic_vector(unsigned(pc_reg) + to_unsigned(BOOT_STRIDE, XLEN));
                                end if;
                                addr_i := unsigned(signed(regs(rs1_i)) + imm_i);
                                addr_i(0) := '0';
                                if decode_next_pc_op = "10" then
                                    pc_reg <= std_logic_vector(addr_i);
                                else
                                    trap_reg <= '1';
                                end if;
                            when "1001" =>
                                if decode_writes_link = '1' and rd_i /= 0 then
                                    regs(rd_i) <= std_logic_vector(unsigned(pc_reg) + to_unsigned(BOOT_STRIDE, XLEN));
                                end if;
                                if decode_next_pc_op = "11" then
                                    pc_reg <= std_logic_vector(unsigned(signed(pc_reg) + jump_i));
                                else
                                    trap_reg <= '1';
                                end if;
                            when "1010" =>
                                pc_reg <= std_logic_vector(unsigned(pc_reg) + to_unsigned(BOOT_STRIDE, XLEN));
                            when others =>
                                trap_reg <= '1';
                        end case;
                    elsif decode_should_halt = '1' then
                        halt_reg <= '1';
                    elsif decode_should_trap = '1' then
                        trap_reg <= '1';
                    end if;
                    regs(0) <= (others => '0');
            end if;
        end if;
    end process;
end architecture rtl;
