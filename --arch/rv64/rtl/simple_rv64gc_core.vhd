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
        irq_software  : in  std_logic;
        irq_timer     : in  std_logic;
        irq_external  : in  std_logic;
        mmu_dmem_l2_pte : in  xword_t;
        mmu_dmem_l1_pte : in  xword_t;
        mmu_dmem_l0_pte : in  xword_t;
        debug_priv_mode : out std_logic_vector(1 downto 0);
        debug_last_load_value : out xword_t;
        debug_ra   : out xword_t;
        debug_sp   : out xword_t;
        debug_s0   : out xword_t;
        debug_a0   : out xword_t;
        debug_a1   : out xword_t;
        debug_a2   : out xword_t;
        debug_load_rd : out xword_t;
        debug_pc      : out xword_t;
        semi_trigger  : out std_logic;
        semi_op       : out xword_t;
        semi_param    : out xword_t;
        trap          : out std_logic;
        halt          : out std_logic
    );
end entity simple_rv64gc_core;

architecture rtl of simple_rv64gc_core is
    type reg_file_t is array (0 to 31) of xword_t;
    alias imem_rdata_raw : std_logic_vector(31 downto 0) is imem_rdata;
    signal pc_reg : xword_t := RESET_VECTOR;
    signal regs : reg_file_t := (2 => x"0000000000000FFC", 10 => x"0000000000000000", 11 => x"0000000088000000", others => (others => '0'));
    signal dmem_addr_reg : xword_t := (others => '0');
    signal dmem_wdata_reg : xword_t := (others => '0');
    signal dmem_we_reg : std_logic := '0';
    signal dmem_re_reg : std_logic := '0';
    signal dmem_width_reg : std_logic_vector(1 downto 0) := "10";
    signal dmem_wstrb_reg : std_logic_vector((XLEN / 8) - 1 downto 0) := (others => '0');
    signal trap_reg : std_logic := '0';
    signal halt_reg : std_logic := '0';
    signal semi_phase_reg : integer range 0 to 2 := 0;
    signal semi_trigger_reg : std_logic := '0';
    signal semi_op_reg : xword_t := (others => '0');
    signal semi_param_reg : xword_t := (others => '0');
    signal priv_mode_reg : std_logic_vector(1 downto 0) := "11";
    signal csr_mstatus_reg : xword_t := (others => '0');
    signal csr_mie_reg : xword_t := (others => '0');
    signal csr_mideleg_reg : xword_t := (others => '0');
    signal csr_medeleg_reg : xword_t := (others => '0');
    signal csr_mtvec_reg : xword_t := (others => '0');
    signal csr_mscratch_reg : xword_t := (others => '0');
    signal csr_mepc_reg : xword_t := (others => '0');
    signal csr_mcause_reg : xword_t := (others => '0');
    signal csr_mtval_reg : xword_t := (others => '0');
    signal csr_stvec_reg : xword_t := (others => '0');
    signal csr_scounteren_reg : xword_t := (others => '0');
    signal csr_sscratch_reg : xword_t := (others => '0');
    signal csr_sepc_reg : xword_t := (others => '0');
    signal csr_scause_reg : xword_t := (others => '0');
    signal csr_stval_reg : xword_t := (others => '0');
    signal csr_satp_reg : xword_t := (others => '0');
    signal csr_mcounteren_reg : xword_t := (others => '0');
    signal debug_last_load_value_reg : xword_t := (others => '0');
    signal load_data_reg : xword_t := (others => '0');
    signal amo_pending_reg : std_logic := '0';
    signal amo_pending_rd_reg : integer range 0 to 31 := 0;
    signal amo_pending_addr_reg : xword_t := (others => '0');
    signal amo_pending_funct3_reg : std_logic_vector(2 downto 0) := (others => '0');
    signal amo_pending_funct5_reg : std_logic_vector(4 downto 0) := (others => '0');
    signal amo_pending_rs2_value_reg : xword_t := (others => '0');
    signal reservation_valid_reg : std_logic := '0';
    signal reservation_addr_reg : xword_t := (others => '0');
    signal load_issue_reg : std_logic := '0';
    signal load_wait_reg : std_logic := '0';
    signal load_settle_reg : std_logic := '0';
    signal load_capture_reg : std_logic := '0';
    signal load_pending_reg : std_logic := '0';
    signal load_writeback_reg : std_logic := '0';
    signal load_pending_rd_reg : integer range 0 to 31 := 0;
    signal load_pending_addr_reg : xword_t := (others => '0');
    signal load_pending_funct3_reg : std_logic_vector(2 downto 0) := (others => '0');
    procedure sv39_translate_data(
        vaddr      : in  xword_t;
        satp       : in  xword_t;
        priv_mode  : in  std_logic_vector(1 downto 0);
        is_write   : in  std_logic;
        l2_pte     : in  xword_t;
        l1_pte     : in  xword_t;
        l0_pte     : in  xword_t;
        paddr      : out xword_t;
        fault      : out std_logic
    ) is
        variable pte_v : xword_t;
        variable translated_v : xword_t;
    begin
        translated_v := vaddr;
        fault := '0';
        if priv_mode = "11" then
            paddr := translated_v;
            return;
        end if;
        if satp(63 downto 60) /= "1000" then
            paddr := translated_v;
            return;
        end if;
        pte_v := l2_pte;
        if pte_v(0) = '0' or (pte_v(2) = '1' and pte_v(1) = '0') then
            fault := '1';
        elsif pte_v(1) = '1' or pte_v(3) = '1' then
            fault := '1';
        else
            pte_v := l1_pte;
            if pte_v(0) = '0' or (pte_v(2) = '1' and pte_v(1) = '0') then
                fault := '1';
            elsif pte_v(1) = '1' or pte_v(3) = '1' then
                fault := '1';
            else
                pte_v := l0_pte;
                if pte_v(0) = '0' or (pte_v(2) = '1' and pte_v(1) = '0') then
                    fault := '1';
                elsif is_write = '1' and pte_v(2) = '0' then
                    fault := '1';
                elsif is_write = '0' and pte_v(1) = '0' then
                    fault := '1';
                elsif priv_mode = "00" and pte_v(4) = '0' then
                    fault := '1';
                elsif priv_mode = "01" and pte_v(4) = '1' then
                    fault := '1';
                elsif pte_v(6) = '0' then
                    fault := '1';
                elsif is_write = '1' and pte_v(7) = '0' then
                    fault := '1';
                else
                    translated_v := (others => '0');
                    translated_v(55 downto 12) := pte_v(53 downto 10);
                    translated_v(11 downto 0) := vaddr(11 downto 0);
                end if;
            end if;
        end if;
        paddr := translated_v;
    end procedure;
begin
    imem_addr <= pc_reg;
    dmem_addr <= dmem_addr_reg;
    dmem_wdata <= dmem_wdata_reg;
    dmem_we <= dmem_we_reg;
    dmem_re <= dmem_re_reg;
    dmem_width <= dmem_width_reg;
    dmem_wstrb <= dmem_wstrb_reg;
    debug_pc <= pc_reg;
    debug_priv_mode <= priv_mode_reg;
    debug_last_load_value <= debug_last_load_value_reg;
    debug_ra <= regs(1);
    debug_sp <= regs(2);
    debug_s0 <= regs(8);
    debug_a0 <= regs(10);
    debug_a1 <= regs(11);
    debug_a2 <= regs(12);
    debug_load_rd <= std_logic_vector(to_unsigned(load_pending_rd_reg, XLEN));
    semi_trigger <= semi_trigger_reg;
    semi_op <= semi_op_reg;
    semi_param <= semi_param_reg;
    trap <= trap_reg;
    halt <= halt_reg;

    process(clk, reset_n)
        variable instr_word_v : std_logic_vector(31 downto 0);
        variable instr_size_bytes : natural range 2 to 4;
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
        variable csr_old_val : xword_t;
        variable csr_new_val : xword_t;
        variable mret_mpp_v : std_logic_vector(1 downto 0);
        variable translated_addr_v : xword_t;
        variable translated_fault_v : std_logic;
        variable atomic_old_word32_v : std_logic_vector(31 downto 0);
        variable atomic_new_word32_v : std_logic_vector(31 downto 0);
        variable atomic_old_word64_v : xword_t;
        variable atomic_new_word64_v : xword_t;
        variable load_should_issue_v : boolean;
    begin
        if reset_n = '0' then
            pc_reg <= RESET_VECTOR;
            regs <= (2 => x"0000000000000FFC", 10 => x"0000000000000000", 11 => x"0000000088000000", others => (others => '0'));
            dmem_addr_reg <= (others => '0');
            dmem_wdata_reg <= (others => '0');
            dmem_we_reg <= '0';
            dmem_re_reg <= '0';
            dmem_width_reg <= "10";
            dmem_wstrb_reg <= (others => '0');
            trap_reg <= '0';
            halt_reg <= '0';
            semi_phase_reg <= 0;
            semi_trigger_reg <= '0';
            semi_op_reg <= (others => '0');
            semi_param_reg <= (others => '0');
            priv_mode_reg <= "11";
            csr_mstatus_reg <= (others => '0');
            csr_mie_reg <= (others => '0');
            csr_mideleg_reg <= (others => '0');
            csr_medeleg_reg <= (others => '0');
            csr_mtvec_reg <= (others => '0');
            csr_mscratch_reg <= (others => '0');
            csr_mepc_reg <= (others => '0');
            csr_mcause_reg <= (others => '0');
            csr_mtval_reg <= (others => '0');
            csr_stvec_reg <= (others => '0');
            csr_scounteren_reg <= (others => '0');
            csr_sscratch_reg <= (others => '0');
            csr_sepc_reg <= (others => '0');
            csr_scause_reg <= (others => '0');
            csr_stval_reg <= (others => '0');
            csr_satp_reg <= (others => '0');
            csr_mcounteren_reg <= (others => '0');
            debug_last_load_value_reg <= (others => '0');
            load_data_reg <= (others => '0');
            amo_pending_reg <= '0';
            amo_pending_rd_reg <= 0;
            amo_pending_addr_reg <= (others => '0');
            amo_pending_funct3_reg <= (others => '0');
            amo_pending_funct5_reg <= (others => '0');
            amo_pending_rs2_value_reg <= (others => '0');
            reservation_valid_reg <= '0';
            reservation_addr_reg <= (others => '0');
            load_issue_reg <= '0';
            load_wait_reg <= '0';
            load_settle_reg <= '0';
            load_capture_reg <= '0';
            load_pending_reg <= '0';
            load_writeback_reg <= '0';
            load_pending_rd_reg <= 0;
            load_pending_addr_reg <= (others => '0');
            load_pending_funct3_reg <= (others => '0');
        elsif rising_edge(clk) then
            dmem_we_reg <= '0';
            dmem_re_reg <= '0';
            dmem_width_reg <= "10";
            dmem_wstrb_reg <= (others => '0');
            semi_trigger_reg <= '0';
            if load_issue_reg = '1' then
                load_issue_reg <= '0';
                load_wait_reg <= '1';
                regs(0) <= (others => '0');
            elsif load_wait_reg = '1' then
                load_wait_reg <= '0';
                load_settle_reg <= '1';
                regs(0) <= (others => '0');
            elsif load_settle_reg = '1' then
                load_settle_reg <= '0';
                load_capture_reg <= '1';
                regs(0) <= (others => '0');
            elsif load_capture_reg = '1' then
                load_capture_reg <= '0';
                load_writeback_reg <= '1';
                load_data_reg <= dmem_rdata;
                regs(0) <= (others => '0');
            elsif load_writeback_reg = '1' then
                addr_i := unsigned(load_pending_addr_reg);
                case load_pending_funct3_reg is
                    when "000" =>
                        if XLEN = 64 then
                            if load_pending_rd_reg /= 0 then
                                regs(load_pending_rd_reg) <= std_logic_vector(resize(signed(shift_right(unsigned(load_data_reg), to_integer(unsigned(addr_i(2 downto 0))) * 8)(7 downto 0)), XLEN));
                                debug_last_load_value_reg <= std_logic_vector(resize(signed(shift_right(unsigned(load_data_reg), to_integer(unsigned(addr_i(2 downto 0))) * 8)(7 downto 0)), XLEN));
                            end if;
                        elsif load_pending_rd_reg /= 0 then
                            regs(load_pending_rd_reg) <= std_logic_vector(resize(signed(shift_right(unsigned(load_data_reg), to_integer(unsigned(addr_i(1 downto 0))) * 8)(7 downto 0)), XLEN));
                            debug_last_load_value_reg <= std_logic_vector(resize(signed(shift_right(unsigned(load_data_reg), to_integer(unsigned(addr_i(1 downto 0))) * 8)(7 downto 0)), XLEN));
                        end if;
                    when "001" =>
                        if XLEN = 64 then
                            if load_pending_rd_reg /= 0 then
                                regs(load_pending_rd_reg) <= std_logic_vector(resize(signed(shift_right(unsigned(load_data_reg), to_integer(unsigned(addr_i(2 downto 0))) * 8)(15 downto 0)), XLEN));
                                debug_last_load_value_reg <= std_logic_vector(resize(signed(shift_right(unsigned(load_data_reg), to_integer(unsigned(addr_i(2 downto 0))) * 8)(15 downto 0)), XLEN));
                            end if;
                        elsif load_pending_rd_reg /= 0 then
                            regs(load_pending_rd_reg) <= std_logic_vector(resize(signed(shift_right(unsigned(load_data_reg), to_integer(unsigned(addr_i(1 downto 0))) * 8)(15 downto 0)), XLEN));
                            debug_last_load_value_reg <= std_logic_vector(resize(signed(shift_right(unsigned(load_data_reg), to_integer(unsigned(addr_i(1 downto 0))) * 8)(15 downto 0)), XLEN));
                        end if;
                    when "010" =>
                        if XLEN = 64 then
                            if load_pending_rd_reg /= 0 then
                                regs(load_pending_rd_reg) <= std_logic_vector(resize(signed(shift_right(unsigned(load_data_reg), to_integer(unsigned(addr_i(2 downto 2))) * 32)(31 downto 0)), XLEN));
                                debug_last_load_value_reg <= std_logic_vector(resize(signed(shift_right(unsigned(load_data_reg), to_integer(unsigned(addr_i(2 downto 2))) * 32)(31 downto 0)), XLEN));
                            end if;
                        elsif load_pending_rd_reg /= 0 then
                            regs(load_pending_rd_reg) <= std_logic_vector(resize(signed(load_data_reg(31 downto 0)), XLEN));
                            debug_last_load_value_reg <= std_logic_vector(resize(signed(load_data_reg(31 downto 0)), XLEN));
                        end if;
                    when "011" =>
                        if XLEN = 64 then
                            if load_pending_rd_reg /= 0 then
                                regs(load_pending_rd_reg) <= load_data_reg;
                                debug_last_load_value_reg <= load_data_reg;
                            end if;
                        else
                            trap_reg <= '1';
                        end if;
                    when "100" =>
                        if XLEN = 64 then
                            if load_pending_rd_reg /= 0 then
                                regs(load_pending_rd_reg) <= std_logic_vector(resize(shift_right(unsigned(load_data_reg), to_integer(unsigned(addr_i(2 downto 0))) * 8)(7 downto 0), XLEN));
                                debug_last_load_value_reg <= std_logic_vector(resize(shift_right(unsigned(load_data_reg), to_integer(unsigned(addr_i(2 downto 0))) * 8)(7 downto 0), XLEN));
                            end if;
                        elsif load_pending_rd_reg /= 0 then
                            regs(load_pending_rd_reg) <= std_logic_vector(resize(shift_right(unsigned(load_data_reg), to_integer(unsigned(addr_i(1 downto 0))) * 8)(7 downto 0), XLEN));
                            debug_last_load_value_reg <= std_logic_vector(resize(shift_right(unsigned(load_data_reg), to_integer(unsigned(addr_i(1 downto 0))) * 8)(7 downto 0), XLEN));
                        end if;
                    when "101" =>
                        if XLEN = 64 then
                            if load_pending_rd_reg /= 0 then
                                regs(load_pending_rd_reg) <= std_logic_vector(resize(shift_right(unsigned(load_data_reg), to_integer(unsigned(addr_i(2 downto 0))) * 8)(15 downto 0), XLEN));
                                debug_last_load_value_reg <= std_logic_vector(resize(shift_right(unsigned(load_data_reg), to_integer(unsigned(addr_i(2 downto 0))) * 8)(15 downto 0), XLEN));
                            end if;
                        elsif load_pending_rd_reg /= 0 then
                            regs(load_pending_rd_reg) <= std_logic_vector(resize(shift_right(unsigned(load_data_reg), to_integer(unsigned(addr_i(1 downto 0))) * 8)(15 downto 0), XLEN));
                            debug_last_load_value_reg <= std_logic_vector(resize(shift_right(unsigned(load_data_reg), to_integer(unsigned(addr_i(1 downto 0))) * 8)(15 downto 0), XLEN));
                        end if;
                    when "110" =>
                        if XLEN = 64 then
                            if load_pending_rd_reg /= 0 then
                                regs(load_pending_rd_reg) <= std_logic_vector(resize(shift_right(unsigned(load_data_reg), to_integer(unsigned(addr_i(2 downto 0))) * 8)(31 downto 0), XLEN));
                                debug_last_load_value_reg <= std_logic_vector(resize(shift_right(unsigned(load_data_reg), to_integer(unsigned(addr_i(2 downto 0))) * 8)(31 downto 0), XLEN));
                            end if;
                        else
                            trap_reg <= '1';
                        end if;
                    when others => trap_reg <= '1';
                end case;
                load_writeback_reg <= '0';
                load_pending_reg <= '0';
                regs(0) <= (others => '0');
            elsif load_pending_reg = '1' then
                regs(0) <= (others => '0');
            elsif amo_pending_reg = '1' then
                addr_i := unsigned(amo_pending_addr_reg);
                atomic_old_word32_v := std_logic_vector(shift_right(unsigned(dmem_rdata), to_integer(unsigned(addr_i(2 downto 0))) * 8)(31 downto 0));
                atomic_old_word64_v := dmem_rdata;
                if amo_pending_funct5_reg = "00010" then
                    reservation_valid_reg <= '1';
                    reservation_addr_reg <= amo_pending_addr_reg;
                    if amo_pending_rd_reg /= 0 then
                        if amo_pending_funct3_reg = "010" then
                            regs(amo_pending_rd_reg) <= std_logic_vector(resize(signed(atomic_old_word32_v), XLEN));
                        elsif XLEN = 64 and amo_pending_funct3_reg = "011" then
                            regs(amo_pending_rd_reg) <= atomic_old_word64_v;
                        else
                            trap_reg <= '1';
                        end if;
                    end if;
                    pc_reg <= std_logic_vector(unsigned(pc_reg) + to_unsigned(4, XLEN));
                elsif amo_pending_funct5_reg = "00011" then
                    if amo_pending_rd_reg /= 0 then
                        if reservation_valid_reg = '1' and reservation_addr_reg = amo_pending_addr_reg then
                            regs(amo_pending_rd_reg) <= (others => '0');
                        else
                            regs(amo_pending_rd_reg) <= std_logic_vector(to_unsigned(1, XLEN));
                        end if;
                    end if;
                    if reservation_valid_reg = '1' and reservation_addr_reg = amo_pending_addr_reg then
                        dmem_addr_reg <= amo_pending_addr_reg;
                        if amo_pending_funct3_reg = "010" then
                            dmem_width_reg <= "10";
                            dmem_wdata_reg <= std_logic_vector(shift_left(unsigned(amo_pending_rs2_value_reg), to_integer(unsigned(addr_i(2 downto 0))) * 8));
                            dmem_wstrb_reg <= std_logic_vector(shift_left(to_unsigned(15, XLEN / 8), to_integer(unsigned(addr_i(2 downto 0)))));
                            dmem_we_reg <= '1';
                        elsif XLEN = 64 and amo_pending_funct3_reg = "011" then
                            dmem_width_reg <= "11";
                            dmem_wdata_reg <= amo_pending_rs2_value_reg;
                            dmem_wstrb_reg <= (others => '1');
                            dmem_we_reg <= '1';
                        else
                            trap_reg <= '1';
                        end if;
                    end if;
                    reservation_valid_reg <= '0';
                    pc_reg <= std_logic_vector(unsigned(pc_reg) + to_unsigned(4, XLEN));
                else
                    if amo_pending_funct3_reg = "010" then
                        if amo_pending_rd_reg /= 0 then
                            regs(amo_pending_rd_reg) <= std_logic_vector(resize(signed(atomic_old_word32_v), XLEN));
                        end if;
                        case amo_pending_funct5_reg is
                            when "00000" => atomic_new_word32_v := std_logic_vector(unsigned(atomic_old_word32_v) + unsigned(amo_pending_rs2_value_reg(31 downto 0)));
                            when "00001" => atomic_new_word32_v := amo_pending_rs2_value_reg(31 downto 0);
                            when "00100" => atomic_new_word32_v := atomic_old_word32_v xor amo_pending_rs2_value_reg(31 downto 0);
                            when "01000" => atomic_new_word32_v := atomic_old_word32_v or amo_pending_rs2_value_reg(31 downto 0);
                            when "01100" => atomic_new_word32_v := atomic_old_word32_v and amo_pending_rs2_value_reg(31 downto 0);
                            when "10000" => if signed(atomic_old_word32_v) < signed(amo_pending_rs2_value_reg(31 downto 0)) then atomic_new_word32_v := atomic_old_word32_v; else atomic_new_word32_v := amo_pending_rs2_value_reg(31 downto 0); end if;
                            when "10100" => if signed(atomic_old_word32_v) > signed(amo_pending_rs2_value_reg(31 downto 0)) then atomic_new_word32_v := atomic_old_word32_v; else atomic_new_word32_v := amo_pending_rs2_value_reg(31 downto 0); end if;
                            when "11000" => if unsigned(atomic_old_word32_v) < unsigned(amo_pending_rs2_value_reg(31 downto 0)) then atomic_new_word32_v := atomic_old_word32_v; else atomic_new_word32_v := amo_pending_rs2_value_reg(31 downto 0); end if;
                            when "11100" => if unsigned(atomic_old_word32_v) > unsigned(amo_pending_rs2_value_reg(31 downto 0)) then atomic_new_word32_v := atomic_old_word32_v; else atomic_new_word32_v := amo_pending_rs2_value_reg(31 downto 0); end if;
                            when others => trap_reg <= '1';
                        end case;
                        if trap_reg = '0' then
                            dmem_addr_reg <= amo_pending_addr_reg;
                            dmem_width_reg <= "10";
                            dmem_wdata_reg <= std_logic_vector(shift_left(resize(unsigned(atomic_new_word32_v), XLEN), to_integer(unsigned(addr_i(2 downto 0))) * 8));
                            dmem_wstrb_reg <= std_logic_vector(shift_left(to_unsigned(15, XLEN / 8), to_integer(unsigned(addr_i(2 downto 0)))));
                            dmem_we_reg <= '1';
                            reservation_valid_reg <= '0';
                            pc_reg <= std_logic_vector(unsigned(pc_reg) + to_unsigned(4, XLEN));
                        end if;
                    elsif XLEN = 64 and amo_pending_funct3_reg = "011" then
                        if amo_pending_rd_reg /= 0 then
                            regs(amo_pending_rd_reg) <= atomic_old_word64_v;
                        end if;
                        case amo_pending_funct5_reg is
                            when "00000" => atomic_new_word64_v := std_logic_vector(unsigned(atomic_old_word64_v) + unsigned(amo_pending_rs2_value_reg));
                            when "00001" => atomic_new_word64_v := amo_pending_rs2_value_reg;
                            when "00100" => atomic_new_word64_v := atomic_old_word64_v xor amo_pending_rs2_value_reg;
                            when "01000" => atomic_new_word64_v := atomic_old_word64_v or amo_pending_rs2_value_reg;
                            when "01100" => atomic_new_word64_v := atomic_old_word64_v and amo_pending_rs2_value_reg;
                            when "10000" => if signed(atomic_old_word64_v) < signed(amo_pending_rs2_value_reg) then atomic_new_word64_v := atomic_old_word64_v; else atomic_new_word64_v := amo_pending_rs2_value_reg; end if;
                            when "10100" => if signed(atomic_old_word64_v) > signed(amo_pending_rs2_value_reg) then atomic_new_word64_v := atomic_old_word64_v; else atomic_new_word64_v := amo_pending_rs2_value_reg; end if;
                            when "11000" => if unsigned(atomic_old_word64_v) < unsigned(amo_pending_rs2_value_reg) then atomic_new_word64_v := atomic_old_word64_v; else atomic_new_word64_v := amo_pending_rs2_value_reg; end if;
                            when "11100" => if unsigned(atomic_old_word64_v) > unsigned(amo_pending_rs2_value_reg) then atomic_new_word64_v := atomic_old_word64_v; else atomic_new_word64_v := amo_pending_rs2_value_reg; end if;
                            when others => trap_reg <= '1';
                        end case;
                        if trap_reg = '0' then
                            dmem_addr_reg <= amo_pending_addr_reg;
                            dmem_width_reg <= "11";
                            dmem_wdata_reg <= atomic_new_word64_v;
                            dmem_wstrb_reg <= (others => '1');
                            dmem_we_reg <= '1';
                            reservation_valid_reg <= '0';
                            pc_reg <= std_logic_vector(unsigned(pc_reg) + to_unsigned(4, XLEN));
                        end if;
                    else
                        trap_reg <= '1';
                    end if;
                end if;
                amo_pending_reg <= '0';
                regs(0) <= (others => '0');
            elsif halt_reg = '0' and trap_reg = '0' then
                if priv_mode_reg /= "11" and csr_mstatus_reg(1) = '1' then
                    if irq_external = '1' and csr_mideleg_reg(9) = '1' and csr_mie_reg(9) = '1' then
                        csr_sepc_reg <= pc_reg;
                        csr_new_val := std_logic_vector(to_unsigned(9, XLEN));
                        csr_new_val(XLEN - 1) := '1';
                        csr_scause_reg <= csr_new_val;
                        csr_stval_reg <= (others => '0');
                        csr_mstatus_reg(5) <= csr_mstatus_reg(1);
                        csr_mstatus_reg(1) <= '0';
                        if priv_mode_reg = "01" then
                            csr_mstatus_reg(8) <= '1';
                        else
                            csr_mstatus_reg(8) <= '0';
                        end if;
                        priv_mode_reg <= "01";
                        pc_reg <= csr_stvec_reg;
                    elsif irq_timer = '1' and csr_mideleg_reg(5) = '1' and csr_mie_reg(5) = '1' then
                        csr_sepc_reg <= pc_reg;
                        csr_new_val := std_logic_vector(to_unsigned(5, XLEN));
                        csr_new_val(XLEN - 1) := '1';
                        csr_scause_reg <= csr_new_val;
                        csr_stval_reg <= (others => '0');
                        csr_mstatus_reg(5) <= csr_mstatus_reg(1);
                        csr_mstatus_reg(1) <= '0';
                        if priv_mode_reg = "01" then
                            csr_mstatus_reg(8) <= '1';
                        else
                            csr_mstatus_reg(8) <= '0';
                        end if;
                        priv_mode_reg <= "01";
                        pc_reg <= csr_stvec_reg;
                    elsif irq_software = '1' and csr_mideleg_reg(1) = '1' and csr_mie_reg(1) = '1' then
                        csr_sepc_reg <= pc_reg;
                        csr_new_val := std_logic_vector(to_unsigned(1, XLEN));
                        csr_new_val(XLEN - 1) := '1';
                        csr_scause_reg <= csr_new_val;
                        csr_stval_reg <= (others => '0');
                        csr_mstatus_reg(5) <= csr_mstatus_reg(1);
                        csr_mstatus_reg(1) <= '0';
                        if priv_mode_reg = "01" then
                            csr_mstatus_reg(8) <= '1';
                        else
                            csr_mstatus_reg(8) <= '0';
                        end if;
                        priv_mode_reg <= "01";
                        pc_reg <= csr_stvec_reg;
                    elsif csr_mstatus_reg(3) = '1' then
                    if irq_external = '1' and csr_mie_reg(11) = '1' then
                        csr_mepc_reg <= pc_reg;
                        csr_new_val := std_logic_vector(to_unsigned(11, XLEN));
                        csr_new_val(XLEN - 1) := '1';
                        csr_mcause_reg <= csr_new_val;
                        csr_mtval_reg <= (others => '0');
                        csr_mstatus_reg(7) <= csr_mstatus_reg(3);
                        csr_mstatus_reg(3) <= '0';
                        csr_mstatus_reg(12 downto 11) <= priv_mode_reg;
                        priv_mode_reg <= "11";
                        pc_reg <= csr_mtvec_reg;
                    elsif irq_timer = '1' and csr_mie_reg(7) = '1' then
                        csr_mepc_reg <= pc_reg;
                        csr_new_val := std_logic_vector(to_unsigned(7, XLEN));
                        csr_new_val(XLEN - 1) := '1';
                        csr_mcause_reg <= csr_new_val;
                        csr_mtval_reg <= (others => '0');
                        csr_mstatus_reg(7) <= csr_mstatus_reg(3);
                        csr_mstatus_reg(3) <= '0';
                        csr_mstatus_reg(12 downto 11) <= priv_mode_reg;
                        priv_mode_reg <= "11";
                        pc_reg <= csr_mtvec_reg;
                    elsif irq_software = '1' and csr_mie_reg(3) = '1' then
                        csr_mepc_reg <= pc_reg;
                        csr_new_val := std_logic_vector(to_unsigned(3, XLEN));
                        csr_new_val(XLEN - 1) := '1';
                        csr_mcause_reg <= csr_new_val;
                        csr_mtval_reg <= (others => '0');
                        csr_mstatus_reg(7) <= csr_mstatus_reg(3);
                        csr_mstatus_reg(3) <= '0';
                        csr_mstatus_reg(12 downto 11) <= priv_mode_reg;
                        priv_mode_reg <= "11";
                        pc_reg <= csr_mtvec_reg;
                    else
                instr_word_v := imem_rdata_raw;
                instr_size_bytes := 4;
                if rv64c_is_compressed(imem_rdata_raw) then
                    instr_word_v := rv64c_decompress(imem_rdata_raw(15 downto 0));
                    instr_size_bytes := 2;
                    if instr_word_v = x"00000000" then
                        trap_reg <= '1';
                    end if;
                end if;
                if instr_word_v = x"01F01013" and semi_phase_reg = 0 then
                    semi_phase_reg <= 1;
                    pc_reg <= std_logic_vector(unsigned(pc_reg) + to_unsigned(instr_size_bytes, XLEN));
                elsif instr_word_v = x"00100073" and semi_phase_reg = 1 then
                    semi_phase_reg <= 2;
                    semi_op_reg <= regs(10);
                    semi_param_reg <= regs(11);
                    pc_reg <= std_logic_vector(unsigned(pc_reg) + to_unsigned(instr_size_bytes, XLEN));
                elsif instr_word_v = x"40705013" and semi_phase_reg = 2 then
                    semi_phase_reg <= 0;
                    semi_trigger_reg <= '1';
                    if semi_op_reg = std_logic_vector(to_unsigned(16#18#, XLEN)) then
                        halt_reg <= '1';
                    else
                        pc_reg <= std_logic_vector(unsigned(pc_reg) + to_unsigned(instr_size_bytes, XLEN));
                    end if;
                elsif instr_word_v = x"00100073" and semi_phase_reg = 0 then
                    halt_reg <= '1';
                else
                rd_i := to_integer(unsigned(instr_word_v(11 downto 7)));
                rs1_i := to_integer(unsigned(instr_word_v(19 downto 15)));
                rs2_i := to_integer(unsigned(instr_word_v(24 downto 20)));
                decode_writeback_bits := instr_word_v;
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
                if instr_word_v(6 downto 0) = "0110111" then
                    decode_dispatch_class_bits := "0000000000000000000000000000" & "0001";
                    decode_trap_halt_control_bits := "00000000000000000000000000000" & '0' & '0' & '1';
                elsif instr_word_v(6 downto 0) = "0010111" then
                    decode_dispatch_class_bits := "0000000000000000000000000000" & "0010";
                    decode_trap_halt_control_bits := "00000000000000000000000000000" & '0' & '0' & '1';
                elsif instr_word_v(6 downto 0) = "0010011" then
                    decode_dispatch_class_bits := "0000000000000000000000000000" & "0011";
                    decode_trap_halt_control_bits := "00000000000000000000000000000" & '0' & '0' & '1';
                elsif instr_word_v(6 downto 0) = "0011011" then
                    decode_dispatch_class_bits := "0000000000000000000000000000" & "1100";
                    decode_trap_halt_control_bits := "00000000000000000000000000000" & '0' & '0' & '1';
                elsif instr_word_v(6 downto 0) = "0110011" then
                    decode_dispatch_class_bits := "0000000000000000000000000000" & "0100";
                    decode_trap_halt_control_bits := "00000000000000000000000000000" & '0' & '0' & '1';
                elsif instr_word_v(6 downto 0) = "0111011" then
                    decode_dispatch_class_bits := "0000000000000000000000000000" & "1101";
                    decode_trap_halt_control_bits := "00000000000000000000000000000" & '0' & '0' & '1';
                elsif instr_word_v(6 downto 0) = "0000011" then
                    decode_dispatch_class_bits := "0000000000000000000000000000" & "0101";
                    decode_trap_halt_control_bits := "00000000000000000000000000000" & '0' & '0' & '1';
                elsif instr_word_v(6 downto 0) = "0100011" then
                    decode_dispatch_class_bits := "0000000000000000000000000000" & "0110";
                    decode_trap_halt_control_bits := "00000000000000000000000000000" & '0' & '0' & '1';
                elsif instr_word_v(6 downto 0) = "1100011" then
                    decode_dispatch_class_bits := "0000000000000000000000000000" & "0111";
                    decode_trap_halt_control_bits := "00000000000000000000000000000" & '0' & '0' & '1';
                elsif instr_word_v(6 downto 0) = "1100111" then
                    decode_dispatch_class_bits := "0000000000000000000000000000" & "1000";
                    decode_trap_halt_control_bits := "00000000000000000000000000000" & '0' & '0' & '1';
                elsif instr_word_v(6 downto 0) = "1101111" then
                    decode_dispatch_class_bits := "0000000000000000000000000000" & "1001";
                    decode_trap_halt_control_bits := "00000000000000000000000000000" & '0' & '0' & '1';
                elsif instr_word_v(6 downto 0) = "0001111" then
                    decode_dispatch_class_bits := "0000000000000000000000000000" & "1010";
                    decode_trap_halt_control_bits := "00000000000000000000000000000" & '0' & '0' & '1';
                elsif instr_word_v(6 downto 0) = "0101111" then
                    decode_dispatch_class_bits := "0000000000000000000000000000" & "1110";
                    decode_trap_halt_control_bits := "00000000000000000000000000000" & '0' & '0' & '1';
                elsif instr_word_v(6 downto 0) = "1110011" then
                    decode_dispatch_class_bits := "0000000000000000000000000000" & "1011";
                    decode_trap_halt_control_bits := "00000000000000000000000000000" & '0' & '0' & '1';
                else
                    decode_trap_halt_control_bits := "00000000000000000000000000000" & '0' & '1' & '0';
                end if;
                case decode_dispatch_class_bits(3 downto 0) is
                    when "0001" | "0010" =>
                        decode_upper_immediate_bits := instr_word_v(31 downto 12) & "000000000000";
                    when "0011" =>
                        decode_writeback_bits := instr_word_v(31 downto 12) & instr_word_v(19 downto 15) & instr_word_v(6 downto 0);
                        decode_i_immediate_bits := "00000000000000000000" & instr_word_v(31 downto 20);
                        decode_execute_control_bits := "0000000000000000000000" & instr_word_v(25 downto 20) & instr_word_v(30 downto 30) & instr_word_v(14 downto 12);
                        if instr_word_v(14 downto 12) = "000" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "0000" & '0';
                        elsif instr_word_v(14 downto 12) = "001" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "0010" & '0';
                        elsif instr_word_v(14 downto 12) = "010" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "0011" & '0';
                        elsif instr_word_v(14 downto 12) = "011" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "0100" & '0';
                        elsif instr_word_v(14 downto 12) = "100" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "0101" & '0';
                        elsif instr_word_v(14 downto 12) = "101" and instr_word_v(30 downto 30) = "0" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "0110" & '0';
                        elsif instr_word_v(14 downto 12) = "101" and instr_word_v(30 downto 30) = "1" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "0111" & '0';
                        elsif instr_word_v(14 downto 12) = "110" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "1000" & '0';
                        elsif instr_word_v(14 downto 12) = "111" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "1001" & '0';
                        end if;
                    when "1100" =>
                        decode_i_immediate_bits := "00000000000000000000" & instr_word_v(31 downto 20);
                        decode_execute_control_bits := "0000000000000000000000" & instr_word_v(25 downto 20) & instr_word_v(30 downto 30) & instr_word_v(14 downto 12);
                        if instr_word_v(14 downto 12) = "000" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "0000" & '0';
                        elsif instr_word_v(14 downto 12) = "001" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "0010" & '0';
                        elsif instr_word_v(14 downto 12) = "101" and instr_word_v(30 downto 30) = "0" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "0110" & '0';
                        elsif instr_word_v(14 downto 12) = "101" and instr_word_v(30 downto 30) = "1" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "0111" & '0';
                        end if;
                    when "0100" =>
                        decode_execute_control_bits := "0000000000000000000000" & instr_word_v(25 downto 20) & instr_word_v(30 downto 30) & instr_word_v(14 downto 12);
                        if instr_word_v(14 downto 12) = "000" and instr_word_v(31 downto 25) = "0000000" then
                            decode_writeback_bits := instr_word_v(31 downto 12) & instr_word_v(24 downto 20) & instr_word_v(6 downto 0);
                        end if;
                        if instr_word_v(31 downto 25) = "0000001" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "1111" & '1';
                        elsif instr_word_v(14 downto 12) = "000" and instr_word_v(30 downto 30) = "0" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "0000" & '1';
                        elsif instr_word_v(14 downto 12) = "000" and instr_word_v(30 downto 30) = "1" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "0001" & '1';
                        elsif instr_word_v(14 downto 12) = "001" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "0010" & '1';
                        elsif instr_word_v(14 downto 12) = "010" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "0011" & '1';
                        elsif instr_word_v(14 downto 12) = "011" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "0100" & '1';
                        elsif instr_word_v(14 downto 12) = "100" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "0101" & '1';
                        elsif instr_word_v(14 downto 12) = "101" and instr_word_v(30 downto 30) = "0" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "0110" & '1';
                        elsif instr_word_v(14 downto 12) = "101" and instr_word_v(30 downto 30) = "1" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "0111" & '1';
                        elsif instr_word_v(14 downto 12) = "110" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "1000" & '1';
                        elsif instr_word_v(14 downto 12) = "111" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "1001" & '1';
                        end if;
                    when "1101" =>
                        decode_execute_control_bits := "0000000000000000000000" & instr_word_v(25 downto 20) & instr_word_v(30 downto 30) & instr_word_v(14 downto 12);
                        if instr_word_v(31 downto 25) = "0000001" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "1111" & '1';
                        elsif instr_word_v(14 downto 12) = "000" and instr_word_v(30 downto 30) = "0" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "0000" & '1';
                        elsif instr_word_v(14 downto 12) = "000" and instr_word_v(30 downto 30) = "1" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "0001" & '1';
                        elsif instr_word_v(14 downto 12) = "001" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "0010" & '1';
                        elsif instr_word_v(14 downto 12) = "101" and instr_word_v(30 downto 30) = "0" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "0110" & '1';
                        elsif instr_word_v(14 downto 12) = "101" and instr_word_v(30 downto 30) = "1" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "0111" & '1';
                        end if;
                    when "0101" =>
                        decode_i_immediate_bits := "00000000000000000000" & instr_word_v(31 downto 20);
                        decode_memory_access_control_bits := "00000000000000000000000000000" & instr_word_v(14 downto 12);
                    when "0110" =>
                        decode_store_immediate_bits := "00000000000000000000" & instr_word_v(31 downto 25) & instr_word_v(11 downto 7);
                        decode_memory_access_control_bits := "00000000000000000000000000000" & instr_word_v(14 downto 12);
                    when "0111" =>
                        decode_branch_immediate_bits := "00000000000000000000" & instr_word_v(31 downto 31) & instr_word_v(7 downto 7) & instr_word_v(30 downto 25) & instr_word_v(11 downto 8);
                        decode_execute_control_bits := "0000000000000000000000" & instr_word_v(25 downto 20) & instr_word_v(30 downto 30) & instr_word_v(14 downto 12);
                        if instr_word_v(14 downto 12) = "000" then
                            decode_branch_datapath_bits := "00000000000000000000000000000" & "000";
                        elsif instr_word_v(14 downto 12) = "001" then
                            decode_branch_datapath_bits := "00000000000000000000000000000" & "001";
                        elsif instr_word_v(14 downto 12) = "100" then
                            decode_branch_datapath_bits := "00000000000000000000000000000" & "010";
                        elsif instr_word_v(14 downto 12) = "101" then
                            decode_branch_datapath_bits := "00000000000000000000000000000" & "011";
                        elsif instr_word_v(14 downto 12) = "110" then
                            decode_branch_datapath_bits := "00000000000000000000000000000" & "100";
                        elsif instr_word_v(14 downto 12) = "111" then
                            decode_branch_datapath_bits := "00000000000000000000000000000" & "101";
                        end if;
                        decode_control_flow_datapath_bits := "00000000000000000000000000000" & '0' & "01";
                    when "1000" =>
                        decode_i_immediate_bits := "00000000000000000000" & instr_word_v(31 downto 20);
                        decode_control_flow_datapath_bits := "00000000000000000000000000000" & '1' & "10";
                    when "1001" =>
                        decode_jump_immediate_bits := "000000000000" & instr_word_v(31 downto 31) & instr_word_v(19 downto 12) & instr_word_v(20 downto 20) & instr_word_v(30 downto 21);
                        decode_control_flow_datapath_bits := "00000000000000000000000000000" & '1' & "11";
                    when others => null;
                end case;
                decode_writeback_rd_i := rd_i;
                imm_i := resize(signed(decode_i_immediate_bits(11 downto 0)), XLEN);
                imm_u := std_logic_vector(resize(signed(decode_upper_immediate_bits), XLEN));
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
                                pc_reg <= std_logic_vector(unsigned(pc_reg) + to_unsigned(instr_size_bytes, XLEN));
                            when "0010" =>
                                if rd_i /= 0 then
                                    regs(rd_i) <= std_logic_vector(signed(pc_reg) + signed(imm_u));
                                end if;
                                pc_reg <= std_logic_vector(unsigned(pc_reg) + to_unsigned(instr_size_bytes, XLEN));
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
                                pc_reg <= std_logic_vector(unsigned(pc_reg) + to_unsigned(instr_size_bytes, XLEN));
                            when "1100" =>
                                if decode_writeback_rd_i /= 0 then
                                    if XLEN = 64 and decode_execute_is_reg = '0' then
                                        case decode_execute_alu_op is
                                            when "0000" => regs(decode_writeback_rd_i) <= std_logic_vector(resize(signed(regs(rs1_i)(31 downto 0)) + signed(imm_i(31 downto 0)), XLEN));
                                            when "0010" => regs(decode_writeback_rd_i) <= std_logic_vector(resize(signed(std_logic_vector(shift_left(unsigned(regs(rs1_i)(31 downto 0)), to_integer(unsigned(instr_word_v(24 downto 20)))))), XLEN));
                                            when "0110" => regs(decode_writeback_rd_i) <= std_logic_vector(resize(signed(std_logic_vector(shift_right(unsigned(regs(rs1_i)(31 downto 0)), to_integer(unsigned(instr_word_v(24 downto 20)))))), XLEN));
                                            when "0111" => regs(decode_writeback_rd_i) <= std_logic_vector(resize(shift_right(signed(regs(rs1_i)(31 downto 0)), to_integer(unsigned(instr_word_v(24 downto 20)))), XLEN));
                                            when others => trap_reg <= '1';
                                        end case;
                                    else
                                        trap_reg <= '1';
                                    end if;
                                end if;
                                pc_reg <= std_logic_vector(unsigned(pc_reg) + to_unsigned(instr_size_bytes, XLEN));
                            when "0100" =>
                                if decode_writeback_rd_i /= 0 then
                                    if decode_execute_is_reg = '1' then
                                        if decode_execute_alu_op = "1111" then
                                            case instr_word_v(14 downto 12) is
                                                when "000" => regs(decode_writeback_rd_i) <= std_logic_vector(resize(signed(regs(rs1_i)) * signed(regs(rs2_i)), XLEN));
                                                when "100" =>
                                                    if regs(rs2_i) = x"0000000000000000" then
                                                        regs(decode_writeback_rd_i) <= (others => '1');
                                                    elsif regs(rs1_i) = x"8000000000000000" and regs(rs2_i) = x"FFFFFFFFFFFFFFFF" then
                                                        regs(decode_writeback_rd_i) <= regs(rs1_i);
                                                    else
                                                        regs(decode_writeback_rd_i) <= std_logic_vector(signed(regs(rs1_i)) / signed(regs(rs2_i)));
                                                    end if;
                                                when "101" =>
                                                    if regs(rs2_i) = x"0000000000000000" then
                                                        regs(decode_writeback_rd_i) <= (others => '1');
                                                    else
                                                        regs(decode_writeback_rd_i) <= std_logic_vector(unsigned(regs(rs1_i)) / unsigned(regs(rs2_i)));
                                                    end if;
                                                when "110" =>
                                                    if regs(rs2_i) = x"0000000000000000" then
                                                        regs(decode_writeback_rd_i) <= regs(rs1_i);
                                                    elsif regs(rs1_i) = x"8000000000000000" and regs(rs2_i) = x"FFFFFFFFFFFFFFFF" then
                                                        regs(decode_writeback_rd_i) <= (others => '0');
                                                    else
                                                        regs(decode_writeback_rd_i) <= std_logic_vector(signed(regs(rs1_i)) rem signed(regs(rs2_i)));
                                                    end if;
                                                when "111" =>
                                                    if regs(rs2_i) = x"0000000000000000" then
                                                        regs(decode_writeback_rd_i) <= regs(rs1_i);
                                                    else
                                                        regs(decode_writeback_rd_i) <= std_logic_vector(unsigned(regs(rs1_i)) rem unsigned(regs(rs2_i)));
                                                    end if;
                                                when others => trap_reg <= '1';
                                            end case;
                                        else
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
                                        end if;
                                    else
                                        trap_reg <= '1';
                                    end if;
                                end if;
                                pc_reg <= std_logic_vector(unsigned(pc_reg) + to_unsigned(instr_size_bytes, XLEN));
                            when "1101" =>
                                if decode_writeback_rd_i /= 0 then
                                    if XLEN = 64 and decode_execute_is_reg = '1' then
                                        if decode_execute_alu_op = "1111" then
                                            case instr_word_v(14 downto 12) is
                                                when "000" => regs(decode_writeback_rd_i) <= std_logic_vector(resize(signed(std_logic_vector(resize(signed(regs(rs1_i)(31 downto 0)) * signed(regs(rs2_i)(31 downto 0)), 32))), XLEN));
                                                when "100" =>
                                                    if regs(rs2_i)(31 downto 0) = x"00000000" then
                                                        regs(decode_writeback_rd_i) <= x"FFFFFFFFFFFFFFFF";
                                                    elsif regs(rs1_i)(31 downto 0) = x"80000000" and regs(rs2_i)(31 downto 0) = x"FFFFFFFF" then
                                                        regs(decode_writeback_rd_i) <= x"FFFFFFFF80000000";
                                                    else
                                                        regs(decode_writeback_rd_i) <= std_logic_vector(resize(signed(std_logic_vector(signed(regs(rs1_i)(31 downto 0)) / signed(regs(rs2_i)(31 downto 0)))), XLEN));
                                                    end if;
                                                when "101" =>
                                                    if regs(rs2_i)(31 downto 0) = x"00000000" then
                                                        regs(decode_writeback_rd_i) <= x"FFFFFFFFFFFFFFFF";
                                                    else
                                                        regs(decode_writeback_rd_i) <= std_logic_vector(resize(signed(std_logic_vector(unsigned(regs(rs1_i)(31 downto 0)) / unsigned(regs(rs2_i)(31 downto 0)))), XLEN));
                                                    end if;
                                                when "110" =>
                                                    if regs(rs2_i)(31 downto 0) = x"00000000" then
                                                        regs(decode_writeback_rd_i) <= std_logic_vector(resize(signed(regs(rs1_i)(31 downto 0)), XLEN));
                                                    elsif regs(rs1_i)(31 downto 0) = x"80000000" and regs(rs2_i)(31 downto 0) = x"FFFFFFFF" then
                                                        regs(decode_writeback_rd_i) <= (others => '0');
                                                    else
                                                        regs(decode_writeback_rd_i) <= std_logic_vector(resize(signed(std_logic_vector(signed(regs(rs1_i)(31 downto 0)) rem signed(regs(rs2_i)(31 downto 0)))), XLEN));
                                                    end if;
                                                when "111" =>
                                                    if regs(rs2_i)(31 downto 0) = x"00000000" then
                                                        regs(decode_writeback_rd_i) <= std_logic_vector(resize(signed(regs(rs1_i)(31 downto 0)), XLEN));
                                                    else
                                                        regs(decode_writeback_rd_i) <= std_logic_vector(resize(signed(std_logic_vector(unsigned(regs(rs1_i)(31 downto 0)) rem unsigned(regs(rs2_i)(31 downto 0)))), XLEN));
                                                    end if;
                                                when others => trap_reg <= '1';
                                            end case;
                                        else
                                        case decode_execute_alu_op is
                                            when "0000" => regs(decode_writeback_rd_i) <= std_logic_vector(resize(signed(regs(rs1_i)(31 downto 0)) + signed(regs(rs2_i)(31 downto 0)), XLEN));
                                            when "0001" => regs(decode_writeback_rd_i) <= std_logic_vector(resize(signed(regs(rs1_i)(31 downto 0)) - signed(regs(rs2_i)(31 downto 0)), XLEN));
                                            when "0010" => regs(decode_writeback_rd_i) <= std_logic_vector(resize(signed(std_logic_vector(shift_left(unsigned(regs(rs1_i)(31 downto 0)), to_integer(unsigned(regs(rs2_i)(4 downto 0)))))), XLEN));
                                            when "0110" => regs(decode_writeback_rd_i) <= std_logic_vector(resize(signed(std_logic_vector(shift_right(unsigned(regs(rs1_i)(31 downto 0)), to_integer(unsigned(regs(rs2_i)(4 downto 0)))))), XLEN));
                                            when "0111" => regs(decode_writeback_rd_i) <= std_logic_vector(resize(shift_right(signed(regs(rs1_i)(31 downto 0)), to_integer(unsigned(regs(rs2_i)(4 downto 0)))), XLEN));
                                            when others => trap_reg <= '1';
                                        end case;
                                        end if;
                                    else
                                        trap_reg <= '1';
                                    end if;
                                end if;
                                pc_reg <= std_logic_vector(unsigned(pc_reg) + to_unsigned(instr_size_bytes, XLEN));
                            when "0101" =>
                                addr_i := unsigned(signed(regs(rs1_i)) + imm_i);
                                sv39_translate_data(std_logic_vector(addr_i), csr_satp_reg, priv_mode_reg, '0', mmu_dmem_l2_pte, mmu_dmem_l1_pte, mmu_dmem_l0_pte, translated_addr_v, translated_fault_v);
                                dmem_addr_reg <= translated_addr_v;
                                dmem_re_reg <= '1';
                                if translated_fault_v = '1' then
                                    dmem_re_reg <= '0';
                                    csr_mepc_reg <= pc_reg;
                                    csr_mcause_reg <= std_logic_vector(to_unsigned(13, XLEN));
                                    csr_mtval_reg <= std_logic_vector(addr_i);
                                    csr_mstatus_reg(7) <= csr_mstatus_reg(3);
                                    csr_mstatus_reg(3) <= '0';
                                    csr_mstatus_reg(12 downto 11) <= priv_mode_reg;
                                    priv_mode_reg <= "11";
                                    pc_reg <= csr_mtvec_reg;
                                else
                                load_should_issue_v := false;
                                case decode_memory_funct3 is
                                    when "000" =>
                                        dmem_width_reg <= "00";
                                        load_should_issue_v := true;
                                    when "001" =>
                                        dmem_width_reg <= "01";
                                        if addr_i(0) = '1' then
                                            trap_reg <= '1';
                                        else
                                            load_should_issue_v := true;
                                        end if;
                                    when "010" =>
                                        dmem_width_reg <= "10";
                                        if addr_i(1 downto 0) /= "00" then
                                            trap_reg <= '1';
                                        else
                                            load_should_issue_v := true;
                                        end if;
                                    when "011" =>
                                        dmem_width_reg <= "11";
                                        if XLEN = 64 then
                                            if addr_i(2 downto 0) /= "000" then
                                                trap_reg <= '1';
                                            else
                                                load_should_issue_v := true;
                                            end if;
                                        else
                                            trap_reg <= '1';
                                        end if;
                                    when "100" =>
                                        dmem_width_reg <= "00";
                                        load_should_issue_v := true;
                                    when "101" =>
                                        dmem_width_reg <= "01";
                                        if addr_i(0) = '1' then
                                            trap_reg <= '1';
                                        else
                                            load_should_issue_v := true;
                                        end if;
                                    when "110" =>
                                        dmem_width_reg <= "10";
                                        if XLEN = 64 then
                                            if addr_i(1 downto 0) /= "00" then
                                                trap_reg <= '1';
                                            else
                                                load_should_issue_v := true;
                                            end if;
                                        else
                                            trap_reg <= '1';
                                        end if;
                                    when others => trap_reg <= '1';
                                end case;
                                if load_should_issue_v then
                                    load_issue_reg <= '1';
                                    load_pending_reg <= '1';
                                    load_pending_rd_reg <= rd_i;
                                    load_pending_addr_reg <= std_logic_vector(addr_i);
                                    load_pending_funct3_reg <= decode_memory_funct3;
                                    pc_reg <= std_logic_vector(unsigned(pc_reg) + to_unsigned(instr_size_bytes, XLEN));
                                else
                                    dmem_re_reg <= '0';
                                end if;
                                end if;
                            when "0110" =>
                                imm_i := resize(signed(decode_store_immediate_bits(11 downto 0)), XLEN);
                                addr_i := unsigned(signed(regs(rs1_i)) + imm_i);
                                sv39_translate_data(std_logic_vector(addr_i), csr_satp_reg, priv_mode_reg, '1', mmu_dmem_l2_pte, mmu_dmem_l1_pte, mmu_dmem_l0_pte, translated_addr_v, translated_fault_v);
                                dmem_addr_reg <= translated_addr_v;
                                if translated_fault_v = '1' then
                                    dmem_we_reg <= '0';
                                    dmem_wstrb_reg <= (others => '0');
                                    csr_mepc_reg <= pc_reg;
                                    csr_mcause_reg <= std_logic_vector(to_unsigned(15, XLEN));
                                    csr_mtval_reg <= std_logic_vector(addr_i);
                                    csr_mstatus_reg(7) <= csr_mstatus_reg(3);
                                    csr_mstatus_reg(3) <= '0';
                                    csr_mstatus_reg(12 downto 11) <= priv_mode_reg;
                                    priv_mode_reg <= "11";
                                    pc_reg <= csr_mtvec_reg;
                                else
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
                                        elsif XLEN = 64 then
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
                                        elsif XLEN = 64 then
                                            dmem_wdata_reg <= std_logic_vector(shift_left(unsigned(regs(rs2_i)), to_integer(unsigned(addr_i(2 downto 0))) * 8));
                                            dmem_wstrb_reg <= std_logic_vector(shift_left(to_unsigned(15, XLEN / 8), to_integer(unsigned(addr_i(2 downto 0)))));
                                            dmem_we_reg <= '1';
                                        elsif XLEN = 32 then
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
                                if trap_reg = '0' then
                                    reservation_valid_reg <= '0';
                                end if;
                                pc_reg <= std_logic_vector(unsigned(pc_reg) + to_unsigned(instr_size_bytes, XLEN));
                                end if;
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
                                    pc_reg <= std_logic_vector(unsigned(pc_reg) + to_unsigned(instr_size_bytes, XLEN));
                                end if;
                            when "1000" =>
                                addr_i := unsigned(signed(regs(rs1_i)) + imm_i);
                                addr_i(0) := '0';
                                if decode_writes_link = '1' and rd_i /= 0 then
                                    regs(rd_i) <= std_logic_vector(unsigned(pc_reg) + to_unsigned(instr_size_bytes, XLEN));
                                end if;
                                if decode_next_pc_op = "10" then
                                    pc_reg <= std_logic_vector(addr_i);
                                else
                                    trap_reg <= '1';
                                end if;
                            when "1001" =>
                                if decode_writes_link = '1' and rd_i /= 0 then
                                    regs(rd_i) <= std_logic_vector(unsigned(pc_reg) + to_unsigned(instr_size_bytes, XLEN));
                                end if;
                                if decode_next_pc_op = "11" then
                                    pc_reg <= std_logic_vector(unsigned(signed(pc_reg) + jump_i));
                                else
                                    trap_reg <= '1';
                                end if;
                            when "1110" =>
                                addr_i := unsigned(regs(rs1_i));
                                sv39_translate_data(std_logic_vector(addr_i), csr_satp_reg, priv_mode_reg, '1', mmu_dmem_l2_pte, mmu_dmem_l1_pte, mmu_dmem_l0_pte, translated_addr_v, translated_fault_v);
                                dmem_addr_reg <= translated_addr_v;
                                dmem_re_reg <= '1';
                                if translated_fault_v = '1' then
                                    dmem_re_reg <= '0';
                                    csr_mepc_reg <= pc_reg;
                                    csr_mcause_reg <= std_logic_vector(to_unsigned(15, XLEN));
                                    csr_mtval_reg <= std_logic_vector(addr_i);
                                    csr_mstatus_reg(7) <= csr_mstatus_reg(3);
                                    csr_mstatus_reg(3) <= '0';
                                    csr_mstatus_reg(12 downto 11) <= priv_mode_reg;
                                    priv_mode_reg <= "11";
                                    pc_reg <= csr_mtvec_reg;
                                else
                                    if instr_word_v(14 downto 12) = "010" then
                                        dmem_width_reg <= "10";
                                        if addr_i(1 downto 0) /= "00" then
                                            trap_reg <= '1';
                                        else
                                            amo_pending_reg <= '1';
                                        end if;
                                    elsif XLEN = 64 and instr_word_v(14 downto 12) = "011" then
                                        dmem_width_reg <= "11";
                                        if addr_i(2 downto 0) /= "000" then
                                            trap_reg <= '1';
                                        else
                                            amo_pending_reg <= '1';
                                        end if;
                                    else
                                        trap_reg <= '1';
                                    end if;
                                    if trap_reg = '0' then
                                        amo_pending_rd_reg <= rd_i;
                                        amo_pending_addr_reg <= translated_addr_v;
                                        amo_pending_funct3_reg <= instr_word_v(14 downto 12);
                                        amo_pending_funct5_reg <= instr_word_v(31 downto 27);
                                        amo_pending_rs2_value_reg <= regs(rs2_i);
                                    end if;
                                end if;
                            when "1010" =>
                                pc_reg <= std_logic_vector(unsigned(pc_reg) + to_unsigned(instr_size_bytes, XLEN));
                            when "1011" =>
                                if instr_word_v(14 downto 12) = "000" then
                                    if instr_word_v = x"00100073" then
                                        halt_reg <= '1';
                                    elsif instr_word_v = x"00000073" then
                                        if priv_mode_reg = "00" and csr_medeleg_reg(8) = '1' then
                                            csr_sepc_reg <= pc_reg;
                                            csr_scause_reg <= std_logic_vector(to_unsigned(8, XLEN));
                                            csr_stval_reg <= (others => '0');
                                            csr_mstatus_reg(5) <= csr_mstatus_reg(1);
                                            csr_mstatus_reg(1) <= '0';
                                            csr_mstatus_reg(8) <= '0';
                                            priv_mode_reg <= "01";
                                            pc_reg <= csr_stvec_reg;
                                        else
                                            csr_mepc_reg <= pc_reg;
                                            if priv_mode_reg = "00" then
                                                csr_mcause_reg <= std_logic_vector(to_unsigned(8, XLEN));
                                            elsif priv_mode_reg = "01" then
                                                csr_mcause_reg <= std_logic_vector(to_unsigned(9, XLEN));
                                            else
                                                csr_mcause_reg <= std_logic_vector(to_unsigned(11, XLEN));
                                            end if;
                                            csr_mtval_reg <= (others => '0');
                                            csr_mstatus_reg(7) <= csr_mstatus_reg(3);
                                            csr_mstatus_reg(3) <= '0';
                                            csr_mstatus_reg(12 downto 11) <= priv_mode_reg;
                                            priv_mode_reg <= "11";
                                            pc_reg <= csr_mtvec_reg;
                                        end if;
                                    elsif instr_word_v = x"30200073" then
                                        mret_mpp_v := csr_mstatus_reg(12 downto 11);
                                        csr_mstatus_reg(3) <= csr_mstatus_reg(7);
                                        csr_mstatus_reg(7) <= '1';
                                        csr_mstatus_reg(12 downto 11) <= "00";
                                        priv_mode_reg <= mret_mpp_v;
                                        pc_reg <= csr_mepc_reg;
                                    elsif instr_word_v = x"10200073" then
                                        csr_mstatus_reg(1) <= csr_mstatus_reg(5);
                                        csr_mstatus_reg(5) <= '1';
                                        if csr_mstatus_reg(8) = '1' then
                                            priv_mode_reg <= "01";
                                        else
                                            priv_mode_reg <= "00";
                                        end if;
                                        csr_mstatus_reg(8) <= '0';
                                        pc_reg <= csr_sepc_reg;
                                    elsif instr_word_v(31 downto 25) = "0001001" then
                                        pc_reg <= std_logic_vector(unsigned(pc_reg) + to_unsigned(instr_size_bytes, XLEN));
                                    else
                                        trap_reg <= '1';
                                    end if;
                                else
                                    csr_old_val := (others => '0');
                                    csr_new_val := (others => '0');
                                    case instr_word_v(31 downto 20) is
                                        when x"100" => csr_old_val := csr_mstatus_reg and x"00000000800DE133";
                                        when x"301" => csr_old_val := x"8000000000141105";
                                        when x"300" => csr_old_val := csr_mstatus_reg;
                                        when x"104" => csr_old_val := csr_mie_reg and csr_mideleg_reg;
                                        when x"304" => csr_old_val := csr_mie_reg;
                                        when x"105" => csr_old_val := csr_stvec_reg;
                                        when x"106" => csr_old_val := csr_scounteren_reg;
                                        when x"305" => csr_old_val := csr_mtvec_reg;
                                        when x"306" => csr_old_val := csr_mcounteren_reg;
                                        when x"140" => csr_old_val := csr_sscratch_reg;
                                        when x"340" => csr_old_val := csr_mscratch_reg;
                                        when x"141" => csr_old_val := csr_sepc_reg;
                                        when x"341" => csr_old_val := csr_mepc_reg;
                                        when x"142" => csr_old_val := csr_scause_reg;
                                        when x"342" => csr_old_val := csr_mcause_reg;
                                        when x"143" => csr_old_val := csr_stval_reg;
                                        when x"180" => csr_old_val := csr_satp_reg;
                                        when x"343" => csr_old_val := csr_mtval_reg;
                                        when x"144" =>
                                            csr_old_val := (others => '0');
                                            csr_old_val(9) := irq_external;
                                            csr_old_val(5) := irq_timer;
                                            csr_old_val(1) := irq_software;
                                            csr_old_val := csr_old_val and csr_mideleg_reg;
                                        when x"302" => csr_old_val := csr_medeleg_reg;
                                        when x"303" => csr_old_val := csr_mideleg_reg;
                                        when x"344" =>
                                            csr_old_val := (others => '0');
                                            csr_old_val(11) := irq_external;
                                            csr_old_val(7) := irq_timer;
                                            csr_old_val(3) := irq_software;
                                        when x"F11" => csr_old_val := (others => '0');
                                        when x"F12" => csr_old_val := (others => '0');
                                        when x"F13" => csr_old_val := (others => '0');
                                        when x"F14" => csr_old_val := (others => '0');
                                        when others => trap_reg <= '1';
                                    end case;
                                    if trap_reg = '0' then
                                        case instr_word_v(14 downto 12) is
                                            when "001" => csr_new_val := regs(rs1_i);
                                            when "010" =>
                                                if rs1_i = 0 then
                                                    csr_new_val := csr_old_val;
                                                else
                                                    csr_new_val := csr_old_val or regs(rs1_i);
                                                end if;
                                            when "011" =>
                                                if rs1_i = 0 then
                                                    csr_new_val := csr_old_val;
                                                else
                                                    csr_new_val := csr_old_val and (not regs(rs1_i));
                                                end if;
                                            when "101" => csr_new_val := std_logic_vector(to_unsigned(rs1_i, XLEN));
                                            when "110" =>
                                                if rs1_i = 0 then
                                                    csr_new_val := csr_old_val;
                                                else
                                                    csr_new_val := csr_old_val or std_logic_vector(to_unsigned(rs1_i, XLEN));
                                                end if;
                                            when "111" =>
                                                if rs1_i = 0 then
                                                    csr_new_val := csr_old_val;
                                                else
                                                    csr_new_val := csr_old_val and (not std_logic_vector(to_unsigned(rs1_i, XLEN)));
                                                end if;
                                            when others => trap_reg <= '1';
                                        end case;
                                    end if;
                                    if trap_reg = '0' then
                                        if rd_i /= 0 then
                                            regs(rd_i) <= csr_old_val;
                                        end if;
                                        case instr_word_v(14 downto 12) is
                                            when "001" | "010" | "011" | "101" | "110" | "111" =>
                                                case instr_word_v(31 downto 20) is
                                                    when x"100" => csr_mstatus_reg <= (csr_mstatus_reg and (not x"00000000800DE133")) or (csr_new_val and x"00000000800DE133");
                                                    when x"300" => csr_mstatus_reg <= csr_new_val;
                                                    when x"104" => csr_mie_reg <= (csr_mie_reg and (not csr_mideleg_reg)) or (csr_new_val and csr_mideleg_reg);
                                                    when x"304" => csr_mie_reg <= csr_new_val;
                                                    when x"105" => csr_stvec_reg <= csr_new_val;
                                                    when x"106" => csr_scounteren_reg <= csr_new_val;
                                                    when x"305" => csr_mtvec_reg <= csr_new_val;
                                                    when x"306" => csr_mcounteren_reg <= csr_new_val;
                                                    when x"140" => csr_sscratch_reg <= csr_new_val;
                                                    when x"340" => csr_mscratch_reg <= csr_new_val;
                                                    when x"141" => csr_sepc_reg <= csr_new_val;
                                                    when x"341" => csr_mepc_reg <= csr_new_val;
                                                    when x"142" => csr_scause_reg <= csr_new_val;
                                                    when x"342" => csr_mcause_reg <= csr_new_val;
                                                    when x"143" => csr_stval_reg <= csr_new_val;
                                                    when x"180" => csr_satp_reg <= csr_new_val;
                                                    when x"343" => csr_mtval_reg <= csr_new_val;
                                                    when x"302" => csr_medeleg_reg <= csr_new_val;
                                                    when x"303" => csr_mideleg_reg <= csr_new_val;
                                                    when others => null;
                                                end case;
                                                pc_reg <= std_logic_vector(unsigned(pc_reg) + to_unsigned(instr_size_bytes, XLEN));
                                            when others => trap_reg <= '1';
                                        end case;
                                    end if;
                                end if;
                            when others =>
                                trap_reg <= '1';
                        end case;
                    elsif decode_should_halt = '1' then
                        halt_reg <= '1';
                    elsif decode_should_trap = '1' then
                        trap_reg <= '1';
                    end if;
                    semi_phase_reg <= 0;
                    regs(0) <= (others => '0');
                end if;
                    end if;
                    else
                instr_word_v := imem_rdata_raw;
                instr_size_bytes := 4;
                if rv64c_is_compressed(imem_rdata_raw) then
                    instr_word_v := rv64c_decompress(imem_rdata_raw(15 downto 0));
                    instr_size_bytes := 2;
                    if instr_word_v = x"00000000" then
                        trap_reg <= '1';
                    end if;
                end if;
                if instr_word_v = x"01F01013" and semi_phase_reg = 0 then
                    semi_phase_reg <= 1;
                    pc_reg <= std_logic_vector(unsigned(pc_reg) + to_unsigned(instr_size_bytes, XLEN));
                elsif instr_word_v = x"00100073" and semi_phase_reg = 1 then
                    semi_phase_reg <= 2;
                    semi_op_reg <= regs(10);
                    semi_param_reg <= regs(11);
                    pc_reg <= std_logic_vector(unsigned(pc_reg) + to_unsigned(instr_size_bytes, XLEN));
                elsif instr_word_v = x"40705013" and semi_phase_reg = 2 then
                    semi_phase_reg <= 0;
                    semi_trigger_reg <= '1';
                    if semi_op_reg = std_logic_vector(to_unsigned(16#18#, XLEN)) then
                        halt_reg <= '1';
                    else
                        pc_reg <= std_logic_vector(unsigned(pc_reg) + to_unsigned(instr_size_bytes, XLEN));
                    end if;
                elsif instr_word_v = x"00100073" and semi_phase_reg = 0 then
                    halt_reg <= '1';
                else
                rd_i := to_integer(unsigned(instr_word_v(11 downto 7)));
                rs1_i := to_integer(unsigned(instr_word_v(19 downto 15)));
                rs2_i := to_integer(unsigned(instr_word_v(24 downto 20)));
                decode_writeback_bits := instr_word_v;
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
                if instr_word_v(6 downto 0) = "0110111" then
                    decode_dispatch_class_bits := "0000000000000000000000000000" & "0001";
                    decode_trap_halt_control_bits := "00000000000000000000000000000" & '0' & '0' & '1';
                elsif instr_word_v(6 downto 0) = "0010111" then
                    decode_dispatch_class_bits := "0000000000000000000000000000" & "0010";
                    decode_trap_halt_control_bits := "00000000000000000000000000000" & '0' & '0' & '1';
                elsif instr_word_v(6 downto 0) = "0010011" then
                    decode_dispatch_class_bits := "0000000000000000000000000000" & "0011";
                    decode_trap_halt_control_bits := "00000000000000000000000000000" & '0' & '0' & '1';
                elsif instr_word_v(6 downto 0) = "0011011" then
                    decode_dispatch_class_bits := "0000000000000000000000000000" & "1100";
                    decode_trap_halt_control_bits := "00000000000000000000000000000" & '0' & '0' & '1';
                elsif instr_word_v(6 downto 0) = "0110011" then
                    decode_dispatch_class_bits := "0000000000000000000000000000" & "0100";
                    decode_trap_halt_control_bits := "00000000000000000000000000000" & '0' & '0' & '1';
                elsif instr_word_v(6 downto 0) = "0111011" then
                    decode_dispatch_class_bits := "0000000000000000000000000000" & "1101";
                    decode_trap_halt_control_bits := "00000000000000000000000000000" & '0' & '0' & '1';
                elsif instr_word_v(6 downto 0) = "0000011" then
                    decode_dispatch_class_bits := "0000000000000000000000000000" & "0101";
                    decode_trap_halt_control_bits := "00000000000000000000000000000" & '0' & '0' & '1';
                elsif instr_word_v(6 downto 0) = "0100011" then
                    decode_dispatch_class_bits := "0000000000000000000000000000" & "0110";
                    decode_trap_halt_control_bits := "00000000000000000000000000000" & '0' & '0' & '1';
                elsif instr_word_v(6 downto 0) = "1100011" then
                    decode_dispatch_class_bits := "0000000000000000000000000000" & "0111";
                    decode_trap_halt_control_bits := "00000000000000000000000000000" & '0' & '0' & '1';
                elsif instr_word_v(6 downto 0) = "1100111" then
                    decode_dispatch_class_bits := "0000000000000000000000000000" & "1000";
                    decode_trap_halt_control_bits := "00000000000000000000000000000" & '0' & '0' & '1';
                elsif instr_word_v(6 downto 0) = "1101111" then
                    decode_dispatch_class_bits := "0000000000000000000000000000" & "1001";
                    decode_trap_halt_control_bits := "00000000000000000000000000000" & '0' & '0' & '1';
                elsif instr_word_v(6 downto 0) = "0001111" then
                    decode_dispatch_class_bits := "0000000000000000000000000000" & "1010";
                    decode_trap_halt_control_bits := "00000000000000000000000000000" & '0' & '0' & '1';
                elsif instr_word_v(6 downto 0) = "0101111" then
                    decode_dispatch_class_bits := "0000000000000000000000000000" & "1110";
                    decode_trap_halt_control_bits := "00000000000000000000000000000" & '0' & '0' & '1';
                elsif instr_word_v(6 downto 0) = "1110011" then
                    decode_dispatch_class_bits := "0000000000000000000000000000" & "1011";
                    decode_trap_halt_control_bits := "00000000000000000000000000000" & '0' & '0' & '1';
                else
                    decode_trap_halt_control_bits := "00000000000000000000000000000" & '0' & '1' & '0';
                end if;
                case decode_dispatch_class_bits(3 downto 0) is
                    when "0001" | "0010" =>
                        decode_upper_immediate_bits := instr_word_v(31 downto 12) & "000000000000";
                    when "0011" =>
                        decode_writeback_bits := instr_word_v(31 downto 12) & instr_word_v(19 downto 15) & instr_word_v(6 downto 0);
                        decode_i_immediate_bits := "00000000000000000000" & instr_word_v(31 downto 20);
                        decode_execute_control_bits := "0000000000000000000000" & instr_word_v(25 downto 20) & instr_word_v(30 downto 30) & instr_word_v(14 downto 12);
                        if instr_word_v(14 downto 12) = "000" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "0000" & '0';
                        elsif instr_word_v(14 downto 12) = "001" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "0010" & '0';
                        elsif instr_word_v(14 downto 12) = "010" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "0011" & '0';
                        elsif instr_word_v(14 downto 12) = "011" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "0100" & '0';
                        elsif instr_word_v(14 downto 12) = "100" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "0101" & '0';
                        elsif instr_word_v(14 downto 12) = "101" and instr_word_v(30 downto 30) = "0" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "0110" & '0';
                        elsif instr_word_v(14 downto 12) = "101" and instr_word_v(30 downto 30) = "1" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "0111" & '0';
                        elsif instr_word_v(14 downto 12) = "110" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "1000" & '0';
                        elsif instr_word_v(14 downto 12) = "111" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "1001" & '0';
                        end if;
                    when "1100" =>
                        decode_i_immediate_bits := "00000000000000000000" & instr_word_v(31 downto 20);
                        decode_execute_control_bits := "0000000000000000000000" & instr_word_v(25 downto 20) & instr_word_v(30 downto 30) & instr_word_v(14 downto 12);
                        if instr_word_v(14 downto 12) = "000" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "0000" & '0';
                        elsif instr_word_v(14 downto 12) = "001" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "0010" & '0';
                        elsif instr_word_v(14 downto 12) = "101" and instr_word_v(30 downto 30) = "0" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "0110" & '0';
                        elsif instr_word_v(14 downto 12) = "101" and instr_word_v(30 downto 30) = "1" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "0111" & '0';
                        end if;
                    when "0100" =>
                        decode_execute_control_bits := "0000000000000000000000" & instr_word_v(25 downto 20) & instr_word_v(30 downto 30) & instr_word_v(14 downto 12);
                        if instr_word_v(14 downto 12) = "000" and instr_word_v(31 downto 25) = "0000000" then
                            decode_writeback_bits := instr_word_v(31 downto 12) & instr_word_v(24 downto 20) & instr_word_v(6 downto 0);
                        end if;
                        if instr_word_v(31 downto 25) = "0000001" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "1111" & '1';
                        elsif instr_word_v(14 downto 12) = "000" and instr_word_v(30 downto 30) = "0" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "0000" & '1';
                        elsif instr_word_v(14 downto 12) = "000" and instr_word_v(30 downto 30) = "1" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "0001" & '1';
                        elsif instr_word_v(14 downto 12) = "001" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "0010" & '1';
                        elsif instr_word_v(14 downto 12) = "010" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "0011" & '1';
                        elsif instr_word_v(14 downto 12) = "011" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "0100" & '1';
                        elsif instr_word_v(14 downto 12) = "100" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "0101" & '1';
                        elsif instr_word_v(14 downto 12) = "101" and instr_word_v(30 downto 30) = "0" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "0110" & '1';
                        elsif instr_word_v(14 downto 12) = "101" and instr_word_v(30 downto 30) = "1" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "0111" & '1';
                        elsif instr_word_v(14 downto 12) = "110" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "1000" & '1';
                        elsif instr_word_v(14 downto 12) = "111" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "1001" & '1';
                        end if;
                    when "1101" =>
                        decode_execute_control_bits := "0000000000000000000000" & instr_word_v(25 downto 20) & instr_word_v(30 downto 30) & instr_word_v(14 downto 12);
                        if instr_word_v(31 downto 25) = "0000001" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "1111" & '1';
                        elsif instr_word_v(14 downto 12) = "000" and instr_word_v(30 downto 30) = "0" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "0000" & '1';
                        elsif instr_word_v(14 downto 12) = "000" and instr_word_v(30 downto 30) = "1" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "0001" & '1';
                        elsif instr_word_v(14 downto 12) = "001" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "0010" & '1';
                        elsif instr_word_v(14 downto 12) = "101" and instr_word_v(30 downto 30) = "0" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "0110" & '1';
                        elsif instr_word_v(14 downto 12) = "101" and instr_word_v(30 downto 30) = "1" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "0111" & '1';
                        end if;
                    when "0101" =>
                        decode_i_immediate_bits := "00000000000000000000" & instr_word_v(31 downto 20);
                        decode_memory_access_control_bits := "00000000000000000000000000000" & instr_word_v(14 downto 12);
                    when "0110" =>
                        decode_store_immediate_bits := "00000000000000000000" & instr_word_v(31 downto 25) & instr_word_v(11 downto 7);
                        decode_memory_access_control_bits := "00000000000000000000000000000" & instr_word_v(14 downto 12);
                    when "0111" =>
                        decode_branch_immediate_bits := "00000000000000000000" & instr_word_v(31 downto 31) & instr_word_v(7 downto 7) & instr_word_v(30 downto 25) & instr_word_v(11 downto 8);
                        decode_execute_control_bits := "0000000000000000000000" & instr_word_v(25 downto 20) & instr_word_v(30 downto 30) & instr_word_v(14 downto 12);
                        if instr_word_v(14 downto 12) = "000" then
                            decode_branch_datapath_bits := "00000000000000000000000000000" & "000";
                        elsif instr_word_v(14 downto 12) = "001" then
                            decode_branch_datapath_bits := "00000000000000000000000000000" & "001";
                        elsif instr_word_v(14 downto 12) = "100" then
                            decode_branch_datapath_bits := "00000000000000000000000000000" & "010";
                        elsif instr_word_v(14 downto 12) = "101" then
                            decode_branch_datapath_bits := "00000000000000000000000000000" & "011";
                        elsif instr_word_v(14 downto 12) = "110" then
                            decode_branch_datapath_bits := "00000000000000000000000000000" & "100";
                        elsif instr_word_v(14 downto 12) = "111" then
                            decode_branch_datapath_bits := "00000000000000000000000000000" & "101";
                        end if;
                        decode_control_flow_datapath_bits := "00000000000000000000000000000" & '0' & "01";
                    when "1000" =>
                        decode_i_immediate_bits := "00000000000000000000" & instr_word_v(31 downto 20);
                        decode_control_flow_datapath_bits := "00000000000000000000000000000" & '1' & "10";
                    when "1001" =>
                        decode_jump_immediate_bits := "000000000000" & instr_word_v(31 downto 31) & instr_word_v(19 downto 12) & instr_word_v(20 downto 20) & instr_word_v(30 downto 21);
                        decode_control_flow_datapath_bits := "00000000000000000000000000000" & '1' & "11";
                    when others => null;
                end case;
                decode_writeback_rd_i := rd_i;
                imm_i := resize(signed(decode_i_immediate_bits(11 downto 0)), XLEN);
                imm_u := std_logic_vector(resize(signed(decode_upper_immediate_bits), XLEN));
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
                                pc_reg <= std_logic_vector(unsigned(pc_reg) + to_unsigned(instr_size_bytes, XLEN));
                            when "0010" =>
                                if rd_i /= 0 then
                                    regs(rd_i) <= std_logic_vector(signed(pc_reg) + signed(imm_u));
                                end if;
                                pc_reg <= std_logic_vector(unsigned(pc_reg) + to_unsigned(instr_size_bytes, XLEN));
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
                                pc_reg <= std_logic_vector(unsigned(pc_reg) + to_unsigned(instr_size_bytes, XLEN));
                            when "1100" =>
                                if decode_writeback_rd_i /= 0 then
                                    if XLEN = 64 and decode_execute_is_reg = '0' then
                                        case decode_execute_alu_op is
                                            when "0000" => regs(decode_writeback_rd_i) <= std_logic_vector(resize(signed(regs(rs1_i)(31 downto 0)) + signed(imm_i(31 downto 0)), XLEN));
                                            when "0010" => regs(decode_writeback_rd_i) <= std_logic_vector(resize(signed(std_logic_vector(shift_left(unsigned(regs(rs1_i)(31 downto 0)), to_integer(unsigned(instr_word_v(24 downto 20)))))), XLEN));
                                            when "0110" => regs(decode_writeback_rd_i) <= std_logic_vector(resize(signed(std_logic_vector(shift_right(unsigned(regs(rs1_i)(31 downto 0)), to_integer(unsigned(instr_word_v(24 downto 20)))))), XLEN));
                                            when "0111" => regs(decode_writeback_rd_i) <= std_logic_vector(resize(shift_right(signed(regs(rs1_i)(31 downto 0)), to_integer(unsigned(instr_word_v(24 downto 20)))), XLEN));
                                            when others => trap_reg <= '1';
                                        end case;
                                    else
                                        trap_reg <= '1';
                                    end if;
                                end if;
                                pc_reg <= std_logic_vector(unsigned(pc_reg) + to_unsigned(instr_size_bytes, XLEN));
                            when "0100" =>
                                if decode_writeback_rd_i /= 0 then
                                    if decode_execute_is_reg = '1' then
                                        if decode_execute_alu_op = "1111" then
                                            case instr_word_v(14 downto 12) is
                                                when "000" => regs(decode_writeback_rd_i) <= std_logic_vector(resize(signed(regs(rs1_i)) * signed(regs(rs2_i)), XLEN));
                                                when "100" =>
                                                    if regs(rs2_i) = x"0000000000000000" then
                                                        regs(decode_writeback_rd_i) <= (others => '1');
                                                    elsif regs(rs1_i) = x"8000000000000000" and regs(rs2_i) = x"FFFFFFFFFFFFFFFF" then
                                                        regs(decode_writeback_rd_i) <= regs(rs1_i);
                                                    else
                                                        regs(decode_writeback_rd_i) <= std_logic_vector(signed(regs(rs1_i)) / signed(regs(rs2_i)));
                                                    end if;
                                                when "101" =>
                                                    if regs(rs2_i) = x"0000000000000000" then
                                                        regs(decode_writeback_rd_i) <= (others => '1');
                                                    else
                                                        regs(decode_writeback_rd_i) <= std_logic_vector(unsigned(regs(rs1_i)) / unsigned(regs(rs2_i)));
                                                    end if;
                                                when "110" =>
                                                    if regs(rs2_i) = x"0000000000000000" then
                                                        regs(decode_writeback_rd_i) <= regs(rs1_i);
                                                    elsif regs(rs1_i) = x"8000000000000000" and regs(rs2_i) = x"FFFFFFFFFFFFFFFF" then
                                                        regs(decode_writeback_rd_i) <= (others => '0');
                                                    else
                                                        regs(decode_writeback_rd_i) <= std_logic_vector(signed(regs(rs1_i)) rem signed(regs(rs2_i)));
                                                    end if;
                                                when "111" =>
                                                    if regs(rs2_i) = x"0000000000000000" then
                                                        regs(decode_writeback_rd_i) <= regs(rs1_i);
                                                    else
                                                        regs(decode_writeback_rd_i) <= std_logic_vector(unsigned(regs(rs1_i)) rem unsigned(regs(rs2_i)));
                                                    end if;
                                                when others => trap_reg <= '1';
                                            end case;
                                        else
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
                                        end if;
                                    else
                                        trap_reg <= '1';
                                    end if;
                                end if;
                                pc_reg <= std_logic_vector(unsigned(pc_reg) + to_unsigned(instr_size_bytes, XLEN));
                            when "1101" =>
                                if decode_writeback_rd_i /= 0 then
                                    if XLEN = 64 and decode_execute_is_reg = '1' then
                                        if decode_execute_alu_op = "1111" then
                                            case instr_word_v(14 downto 12) is
                                                when "000" => regs(decode_writeback_rd_i) <= std_logic_vector(resize(signed(std_logic_vector(resize(signed(regs(rs1_i)(31 downto 0)) * signed(regs(rs2_i)(31 downto 0)), 32))), XLEN));
                                                when "100" =>
                                                    if regs(rs2_i)(31 downto 0) = x"00000000" then
                                                        regs(decode_writeback_rd_i) <= x"FFFFFFFFFFFFFFFF";
                                                    elsif regs(rs1_i)(31 downto 0) = x"80000000" and regs(rs2_i)(31 downto 0) = x"FFFFFFFF" then
                                                        regs(decode_writeback_rd_i) <= x"FFFFFFFF80000000";
                                                    else
                                                        regs(decode_writeback_rd_i) <= std_logic_vector(resize(signed(std_logic_vector(signed(regs(rs1_i)(31 downto 0)) / signed(regs(rs2_i)(31 downto 0)))), XLEN));
                                                    end if;
                                                when "101" =>
                                                    if regs(rs2_i)(31 downto 0) = x"00000000" then
                                                        regs(decode_writeback_rd_i) <= x"FFFFFFFFFFFFFFFF";
                                                    else
                                                        regs(decode_writeback_rd_i) <= std_logic_vector(resize(signed(std_logic_vector(unsigned(regs(rs1_i)(31 downto 0)) / unsigned(regs(rs2_i)(31 downto 0)))), XLEN));
                                                    end if;
                                                when "110" =>
                                                    if regs(rs2_i)(31 downto 0) = x"00000000" then
                                                        regs(decode_writeback_rd_i) <= std_logic_vector(resize(signed(regs(rs1_i)(31 downto 0)), XLEN));
                                                    elsif regs(rs1_i)(31 downto 0) = x"80000000" and regs(rs2_i)(31 downto 0) = x"FFFFFFFF" then
                                                        regs(decode_writeback_rd_i) <= (others => '0');
                                                    else
                                                        regs(decode_writeback_rd_i) <= std_logic_vector(resize(signed(std_logic_vector(signed(regs(rs1_i)(31 downto 0)) rem signed(regs(rs2_i)(31 downto 0)))), XLEN));
                                                    end if;
                                                when "111" =>
                                                    if regs(rs2_i)(31 downto 0) = x"00000000" then
                                                        regs(decode_writeback_rd_i) <= std_logic_vector(resize(signed(regs(rs1_i)(31 downto 0)), XLEN));
                                                    else
                                                        regs(decode_writeback_rd_i) <= std_logic_vector(resize(signed(std_logic_vector(unsigned(regs(rs1_i)(31 downto 0)) rem unsigned(regs(rs2_i)(31 downto 0)))), XLEN));
                                                    end if;
                                                when others => trap_reg <= '1';
                                            end case;
                                        else
                                        case decode_execute_alu_op is
                                            when "0000" => regs(decode_writeback_rd_i) <= std_logic_vector(resize(signed(regs(rs1_i)(31 downto 0)) + signed(regs(rs2_i)(31 downto 0)), XLEN));
                                            when "0001" => regs(decode_writeback_rd_i) <= std_logic_vector(resize(signed(regs(rs1_i)(31 downto 0)) - signed(regs(rs2_i)(31 downto 0)), XLEN));
                                            when "0010" => regs(decode_writeback_rd_i) <= std_logic_vector(resize(signed(std_logic_vector(shift_left(unsigned(regs(rs1_i)(31 downto 0)), to_integer(unsigned(regs(rs2_i)(4 downto 0)))))), XLEN));
                                            when "0110" => regs(decode_writeback_rd_i) <= std_logic_vector(resize(signed(std_logic_vector(shift_right(unsigned(regs(rs1_i)(31 downto 0)), to_integer(unsigned(regs(rs2_i)(4 downto 0)))))), XLEN));
                                            when "0111" => regs(decode_writeback_rd_i) <= std_logic_vector(resize(shift_right(signed(regs(rs1_i)(31 downto 0)), to_integer(unsigned(regs(rs2_i)(4 downto 0)))), XLEN));
                                            when others => trap_reg <= '1';
                                        end case;
                                        end if;
                                    else
                                        trap_reg <= '1';
                                    end if;
                                end if;
                                pc_reg <= std_logic_vector(unsigned(pc_reg) + to_unsigned(instr_size_bytes, XLEN));
                            when "0101" =>
                                addr_i := unsigned(signed(regs(rs1_i)) + imm_i);
                                sv39_translate_data(std_logic_vector(addr_i), csr_satp_reg, priv_mode_reg, '0', mmu_dmem_l2_pte, mmu_dmem_l1_pte, mmu_dmem_l0_pte, translated_addr_v, translated_fault_v);
                                dmem_addr_reg <= translated_addr_v;
                                dmem_re_reg <= '1';
                                if translated_fault_v = '1' then
                                    dmem_re_reg <= '0';
                                    csr_mepc_reg <= pc_reg;
                                    csr_mcause_reg <= std_logic_vector(to_unsigned(13, XLEN));
                                    csr_mtval_reg <= std_logic_vector(addr_i);
                                    csr_mstatus_reg(7) <= csr_mstatus_reg(3);
                                    csr_mstatus_reg(3) <= '0';
                                    csr_mstatus_reg(12 downto 11) <= priv_mode_reg;
                                    priv_mode_reg <= "11";
                                    pc_reg <= csr_mtvec_reg;
                                else
                                load_should_issue_v := false;
                                case decode_memory_funct3 is
                                    when "000" =>
                                        dmem_width_reg <= "00";
                                        load_should_issue_v := true;
                                    when "001" =>
                                        dmem_width_reg <= "01";
                                        if addr_i(0) = '1' then
                                            trap_reg <= '1';
                                        else
                                            load_should_issue_v := true;
                                        end if;
                                    when "010" =>
                                        dmem_width_reg <= "10";
                                        if addr_i(1 downto 0) /= "00" then
                                            trap_reg <= '1';
                                        else
                                            load_should_issue_v := true;
                                        end if;
                                    when "011" =>
                                        dmem_width_reg <= "11";
                                        if XLEN = 64 then
                                            if addr_i(2 downto 0) /= "000" then
                                                trap_reg <= '1';
                                            else
                                                load_should_issue_v := true;
                                            end if;
                                        else
                                            trap_reg <= '1';
                                        end if;
                                    when "100" =>
                                        dmem_width_reg <= "00";
                                        load_should_issue_v := true;
                                    when "101" =>
                                        dmem_width_reg <= "01";
                                        if addr_i(0) = '1' then
                                            trap_reg <= '1';
                                        else
                                            load_should_issue_v := true;
                                        end if;
                                    when "110" =>
                                        dmem_width_reg <= "10";
                                        if XLEN = 64 then
                                            if addr_i(1 downto 0) /= "00" then
                                                trap_reg <= '1';
                                            else
                                                load_should_issue_v := true;
                                            end if;
                                        else
                                            trap_reg <= '1';
                                        end if;
                                    when others => trap_reg <= '1';
                                end case;
                                if load_should_issue_v then
                                    load_issue_reg <= '1';
                                    load_pending_reg <= '1';
                                    load_pending_rd_reg <= rd_i;
                                    load_pending_addr_reg <= std_logic_vector(addr_i);
                                    load_pending_funct3_reg <= decode_memory_funct3;
                                    pc_reg <= std_logic_vector(unsigned(pc_reg) + to_unsigned(instr_size_bytes, XLEN));
                                else
                                    dmem_re_reg <= '0';
                                end if;
                                end if;
                            when "0110" =>
                                imm_i := resize(signed(decode_store_immediate_bits(11 downto 0)), XLEN);
                                addr_i := unsigned(signed(regs(rs1_i)) + imm_i);
                                sv39_translate_data(std_logic_vector(addr_i), csr_satp_reg, priv_mode_reg, '1', mmu_dmem_l2_pte, mmu_dmem_l1_pte, mmu_dmem_l0_pte, translated_addr_v, translated_fault_v);
                                dmem_addr_reg <= translated_addr_v;
                                if translated_fault_v = '1' then
                                    dmem_we_reg <= '0';
                                    dmem_wstrb_reg <= (others => '0');
                                    csr_mepc_reg <= pc_reg;
                                    csr_mcause_reg <= std_logic_vector(to_unsigned(15, XLEN));
                                    csr_mtval_reg <= std_logic_vector(addr_i);
                                    csr_mstatus_reg(7) <= csr_mstatus_reg(3);
                                    csr_mstatus_reg(3) <= '0';
                                    csr_mstatus_reg(12 downto 11) <= priv_mode_reg;
                                    priv_mode_reg <= "11";
                                    pc_reg <= csr_mtvec_reg;
                                else
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
                                        elsif XLEN = 64 then
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
                                        elsif XLEN = 64 then
                                            dmem_wdata_reg <= std_logic_vector(shift_left(unsigned(regs(rs2_i)), to_integer(unsigned(addr_i(2 downto 0))) * 8));
                                            dmem_wstrb_reg <= std_logic_vector(shift_left(to_unsigned(15, XLEN / 8), to_integer(unsigned(addr_i(2 downto 0)))));
                                            dmem_we_reg <= '1';
                                        elsif XLEN = 32 then
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
                                if trap_reg = '0' then
                                    reservation_valid_reg <= '0';
                                end if;
                                pc_reg <= std_logic_vector(unsigned(pc_reg) + to_unsigned(instr_size_bytes, XLEN));
                                end if;
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
                                    pc_reg <= std_logic_vector(unsigned(pc_reg) + to_unsigned(instr_size_bytes, XLEN));
                                end if;
                            when "1000" =>
                                addr_i := unsigned(signed(regs(rs1_i)) + imm_i);
                                addr_i(0) := '0';
                                if decode_writes_link = '1' and rd_i /= 0 then
                                    regs(rd_i) <= std_logic_vector(unsigned(pc_reg) + to_unsigned(instr_size_bytes, XLEN));
                                end if;
                                if decode_next_pc_op = "10" then
                                    pc_reg <= std_logic_vector(addr_i);
                                else
                                    trap_reg <= '1';
                                end if;
                            when "1001" =>
                                if decode_writes_link = '1' and rd_i /= 0 then
                                    regs(rd_i) <= std_logic_vector(unsigned(pc_reg) + to_unsigned(instr_size_bytes, XLEN));
                                end if;
                                if decode_next_pc_op = "11" then
                                    pc_reg <= std_logic_vector(unsigned(signed(pc_reg) + jump_i));
                                else
                                    trap_reg <= '1';
                                end if;
                            when "1110" =>
                                addr_i := unsigned(regs(rs1_i));
                                sv39_translate_data(std_logic_vector(addr_i), csr_satp_reg, priv_mode_reg, '1', mmu_dmem_l2_pte, mmu_dmem_l1_pte, mmu_dmem_l0_pte, translated_addr_v, translated_fault_v);
                                dmem_addr_reg <= translated_addr_v;
                                dmem_re_reg <= '1';
                                if translated_fault_v = '1' then
                                    dmem_re_reg <= '0';
                                    csr_mepc_reg <= pc_reg;
                                    csr_mcause_reg <= std_logic_vector(to_unsigned(15, XLEN));
                                    csr_mtval_reg <= std_logic_vector(addr_i);
                                    csr_mstatus_reg(7) <= csr_mstatus_reg(3);
                                    csr_mstatus_reg(3) <= '0';
                                    csr_mstatus_reg(12 downto 11) <= priv_mode_reg;
                                    priv_mode_reg <= "11";
                                    pc_reg <= csr_mtvec_reg;
                                else
                                    if instr_word_v(14 downto 12) = "010" then
                                        dmem_width_reg <= "10";
                                        if addr_i(1 downto 0) /= "00" then
                                            trap_reg <= '1';
                                        else
                                            amo_pending_reg <= '1';
                                        end if;
                                    elsif XLEN = 64 and instr_word_v(14 downto 12) = "011" then
                                        dmem_width_reg <= "11";
                                        if addr_i(2 downto 0) /= "000" then
                                            trap_reg <= '1';
                                        else
                                            amo_pending_reg <= '1';
                                        end if;
                                    else
                                        trap_reg <= '1';
                                    end if;
                                    if trap_reg = '0' then
                                        amo_pending_rd_reg <= rd_i;
                                        amo_pending_addr_reg <= translated_addr_v;
                                        amo_pending_funct3_reg <= instr_word_v(14 downto 12);
                                        amo_pending_funct5_reg <= instr_word_v(31 downto 27);
                                        amo_pending_rs2_value_reg <= regs(rs2_i);
                                    end if;
                                end if;
                            when "1010" =>
                                pc_reg <= std_logic_vector(unsigned(pc_reg) + to_unsigned(instr_size_bytes, XLEN));
                            when "1011" =>
                                if instr_word_v(14 downto 12) = "000" then
                                    if instr_word_v = x"00100073" then
                                        halt_reg <= '1';
                                    elsif instr_word_v = x"00000073" then
                                        if priv_mode_reg = "00" and csr_medeleg_reg(8) = '1' then
                                            csr_sepc_reg <= pc_reg;
                                            csr_scause_reg <= std_logic_vector(to_unsigned(8, XLEN));
                                            csr_stval_reg <= (others => '0');
                                            csr_mstatus_reg(5) <= csr_mstatus_reg(1);
                                            csr_mstatus_reg(1) <= '0';
                                            csr_mstatus_reg(8) <= '0';
                                            priv_mode_reg <= "01";
                                            pc_reg <= csr_stvec_reg;
                                        else
                                            csr_mepc_reg <= pc_reg;
                                            if priv_mode_reg = "00" then
                                                csr_mcause_reg <= std_logic_vector(to_unsigned(8, XLEN));
                                            elsif priv_mode_reg = "01" then
                                                csr_mcause_reg <= std_logic_vector(to_unsigned(9, XLEN));
                                            else
                                                csr_mcause_reg <= std_logic_vector(to_unsigned(11, XLEN));
                                            end if;
                                            csr_mtval_reg <= (others => '0');
                                            csr_mstatus_reg(7) <= csr_mstatus_reg(3);
                                            csr_mstatus_reg(3) <= '0';
                                            csr_mstatus_reg(12 downto 11) <= priv_mode_reg;
                                            priv_mode_reg <= "11";
                                            pc_reg <= csr_mtvec_reg;
                                        end if;
                                    elsif instr_word_v = x"30200073" then
                                        mret_mpp_v := csr_mstatus_reg(12 downto 11);
                                        csr_mstatus_reg(3) <= csr_mstatus_reg(7);
                                        csr_mstatus_reg(7) <= '1';
                                        csr_mstatus_reg(12 downto 11) <= "00";
                                        priv_mode_reg <= mret_mpp_v;
                                        pc_reg <= csr_mepc_reg;
                                    elsif instr_word_v = x"10200073" then
                                        csr_mstatus_reg(1) <= csr_mstatus_reg(5);
                                        csr_mstatus_reg(5) <= '1';
                                        if csr_mstatus_reg(8) = '1' then
                                            priv_mode_reg <= "01";
                                        else
                                            priv_mode_reg <= "00";
                                        end if;
                                        csr_mstatus_reg(8) <= '0';
                                        pc_reg <= csr_sepc_reg;
                                    elsif instr_word_v(31 downto 25) = "0001001" then
                                        pc_reg <= std_logic_vector(unsigned(pc_reg) + to_unsigned(instr_size_bytes, XLEN));
                                    else
                                        trap_reg <= '1';
                                    end if;
                                else
                                    csr_old_val := (others => '0');
                                    csr_new_val := (others => '0');
                                    case instr_word_v(31 downto 20) is
                                        when x"100" => csr_old_val := csr_mstatus_reg and x"00000000800DE133";
                                        when x"301" => csr_old_val := x"8000000000141105";
                                        when x"300" => csr_old_val := csr_mstatus_reg;
                                        when x"104" => csr_old_val := csr_mie_reg and csr_mideleg_reg;
                                        when x"304" => csr_old_val := csr_mie_reg;
                                        when x"105" => csr_old_val := csr_stvec_reg;
                                        when x"106" => csr_old_val := csr_scounteren_reg;
                                        when x"305" => csr_old_val := csr_mtvec_reg;
                                        when x"306" => csr_old_val := csr_mcounteren_reg;
                                        when x"140" => csr_old_val := csr_sscratch_reg;
                                        when x"340" => csr_old_val := csr_mscratch_reg;
                                        when x"141" => csr_old_val := csr_sepc_reg;
                                        when x"341" => csr_old_val := csr_mepc_reg;
                                        when x"142" => csr_old_val := csr_scause_reg;
                                        when x"342" => csr_old_val := csr_mcause_reg;
                                        when x"143" => csr_old_val := csr_stval_reg;
                                        when x"180" => csr_old_val := csr_satp_reg;
                                        when x"343" => csr_old_val := csr_mtval_reg;
                                        when x"144" =>
                                            csr_old_val := (others => '0');
                                            csr_old_val(9) := irq_external;
                                            csr_old_val(5) := irq_timer;
                                            csr_old_val(1) := irq_software;
                                            csr_old_val := csr_old_val and csr_mideleg_reg;
                                        when x"302" => csr_old_val := csr_medeleg_reg;
                                        when x"303" => csr_old_val := csr_mideleg_reg;
                                        when x"344" =>
                                            csr_old_val := (others => '0');
                                            csr_old_val(11) := irq_external;
                                            csr_old_val(7) := irq_timer;
                                            csr_old_val(3) := irq_software;
                                        when x"F11" => csr_old_val := (others => '0');
                                        when x"F12" => csr_old_val := (others => '0');
                                        when x"F13" => csr_old_val := (others => '0');
                                        when x"F14" => csr_old_val := (others => '0');
                                        when others => trap_reg <= '1';
                                    end case;
                                    if trap_reg = '0' then
                                        case instr_word_v(14 downto 12) is
                                            when "001" => csr_new_val := regs(rs1_i);
                                            when "010" =>
                                                if rs1_i = 0 then
                                                    csr_new_val := csr_old_val;
                                                else
                                                    csr_new_val := csr_old_val or regs(rs1_i);
                                                end if;
                                            when "011" =>
                                                if rs1_i = 0 then
                                                    csr_new_val := csr_old_val;
                                                else
                                                    csr_new_val := csr_old_val and (not regs(rs1_i));
                                                end if;
                                            when "101" => csr_new_val := std_logic_vector(to_unsigned(rs1_i, XLEN));
                                            when "110" =>
                                                if rs1_i = 0 then
                                                    csr_new_val := csr_old_val;
                                                else
                                                    csr_new_val := csr_old_val or std_logic_vector(to_unsigned(rs1_i, XLEN));
                                                end if;
                                            when "111" =>
                                                if rs1_i = 0 then
                                                    csr_new_val := csr_old_val;
                                                else
                                                    csr_new_val := csr_old_val and (not std_logic_vector(to_unsigned(rs1_i, XLEN)));
                                                end if;
                                            when others => trap_reg <= '1';
                                        end case;
                                    end if;
                                    if trap_reg = '0' then
                                        if rd_i /= 0 then
                                            regs(rd_i) <= csr_old_val;
                                        end if;
                                        case instr_word_v(14 downto 12) is
                                            when "001" | "010" | "011" | "101" | "110" | "111" =>
                                                case instr_word_v(31 downto 20) is
                                                    when x"100" => csr_mstatus_reg <= (csr_mstatus_reg and (not x"00000000800DE133")) or (csr_new_val and x"00000000800DE133");
                                                    when x"300" => csr_mstatus_reg <= csr_new_val;
                                                    when x"104" => csr_mie_reg <= (csr_mie_reg and (not csr_mideleg_reg)) or (csr_new_val and csr_mideleg_reg);
                                                    when x"304" => csr_mie_reg <= csr_new_val;
                                                    when x"105" => csr_stvec_reg <= csr_new_val;
                                                    when x"106" => csr_scounteren_reg <= csr_new_val;
                                                    when x"305" => csr_mtvec_reg <= csr_new_val;
                                                    when x"306" => csr_mcounteren_reg <= csr_new_val;
                                                    when x"140" => csr_sscratch_reg <= csr_new_val;
                                                    when x"340" => csr_mscratch_reg <= csr_new_val;
                                                    when x"141" => csr_sepc_reg <= csr_new_val;
                                                    when x"341" => csr_mepc_reg <= csr_new_val;
                                                    when x"142" => csr_scause_reg <= csr_new_val;
                                                    when x"342" => csr_mcause_reg <= csr_new_val;
                                                    when x"143" => csr_stval_reg <= csr_new_val;
                                                    when x"180" => csr_satp_reg <= csr_new_val;
                                                    when x"343" => csr_mtval_reg <= csr_new_val;
                                                    when x"302" => csr_medeleg_reg <= csr_new_val;
                                                    when x"303" => csr_mideleg_reg <= csr_new_val;
                                                    when others => null;
                                                end case;
                                                pc_reg <= std_logic_vector(unsigned(pc_reg) + to_unsigned(instr_size_bytes, XLEN));
                                            when others => trap_reg <= '1';
                                        end case;
                                    end if;
                                end if;
                            when others =>
                                trap_reg <= '1';
                        end case;
                    elsif decode_should_halt = '1' then
                        halt_reg <= '1';
                    elsif decode_should_trap = '1' then
                        trap_reg <= '1';
                    end if;
                    semi_phase_reg <= 0;
                    regs(0) <= (others => '0');
                end if;
                    end if;
                else
                instr_word_v := imem_rdata_raw;
                instr_size_bytes := 4;
                if rv64c_is_compressed(imem_rdata_raw) then
                    instr_word_v := rv64c_decompress(imem_rdata_raw(15 downto 0));
                    instr_size_bytes := 2;
                    if instr_word_v = x"00000000" then
                        trap_reg <= '1';
                    end if;
                end if;
                if instr_word_v = x"01F01013" and semi_phase_reg = 0 then
                    semi_phase_reg <= 1;
                    pc_reg <= std_logic_vector(unsigned(pc_reg) + to_unsigned(instr_size_bytes, XLEN));
                elsif instr_word_v = x"00100073" and semi_phase_reg = 1 then
                    semi_phase_reg <= 2;
                    semi_op_reg <= regs(10);
                    semi_param_reg <= regs(11);
                    pc_reg <= std_logic_vector(unsigned(pc_reg) + to_unsigned(instr_size_bytes, XLEN));
                elsif instr_word_v = x"40705013" and semi_phase_reg = 2 then
                    semi_phase_reg <= 0;
                    semi_trigger_reg <= '1';
                    if semi_op_reg = std_logic_vector(to_unsigned(16#18#, XLEN)) then
                        halt_reg <= '1';
                    else
                        pc_reg <= std_logic_vector(unsigned(pc_reg) + to_unsigned(instr_size_bytes, XLEN));
                    end if;
                elsif instr_word_v = x"00100073" and semi_phase_reg = 0 then
                    halt_reg <= '1';
                else
                rd_i := to_integer(unsigned(instr_word_v(11 downto 7)));
                rs1_i := to_integer(unsigned(instr_word_v(19 downto 15)));
                rs2_i := to_integer(unsigned(instr_word_v(24 downto 20)));
                decode_writeback_bits := instr_word_v;
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
                if instr_word_v(6 downto 0) = "0110111" then
                    decode_dispatch_class_bits := "0000000000000000000000000000" & "0001";
                    decode_trap_halt_control_bits := "00000000000000000000000000000" & '0' & '0' & '1';
                elsif instr_word_v(6 downto 0) = "0010111" then
                    decode_dispatch_class_bits := "0000000000000000000000000000" & "0010";
                    decode_trap_halt_control_bits := "00000000000000000000000000000" & '0' & '0' & '1';
                elsif instr_word_v(6 downto 0) = "0010011" then
                    decode_dispatch_class_bits := "0000000000000000000000000000" & "0011";
                    decode_trap_halt_control_bits := "00000000000000000000000000000" & '0' & '0' & '1';
                elsif instr_word_v(6 downto 0) = "0011011" then
                    decode_dispatch_class_bits := "0000000000000000000000000000" & "1100";
                    decode_trap_halt_control_bits := "00000000000000000000000000000" & '0' & '0' & '1';
                elsif instr_word_v(6 downto 0) = "0110011" then
                    decode_dispatch_class_bits := "0000000000000000000000000000" & "0100";
                    decode_trap_halt_control_bits := "00000000000000000000000000000" & '0' & '0' & '1';
                elsif instr_word_v(6 downto 0) = "0111011" then
                    decode_dispatch_class_bits := "0000000000000000000000000000" & "1101";
                    decode_trap_halt_control_bits := "00000000000000000000000000000" & '0' & '0' & '1';
                elsif instr_word_v(6 downto 0) = "0000011" then
                    decode_dispatch_class_bits := "0000000000000000000000000000" & "0101";
                    decode_trap_halt_control_bits := "00000000000000000000000000000" & '0' & '0' & '1';
                elsif instr_word_v(6 downto 0) = "0100011" then
                    decode_dispatch_class_bits := "0000000000000000000000000000" & "0110";
                    decode_trap_halt_control_bits := "00000000000000000000000000000" & '0' & '0' & '1';
                elsif instr_word_v(6 downto 0) = "1100011" then
                    decode_dispatch_class_bits := "0000000000000000000000000000" & "0111";
                    decode_trap_halt_control_bits := "00000000000000000000000000000" & '0' & '0' & '1';
                elsif instr_word_v(6 downto 0) = "1100111" then
                    decode_dispatch_class_bits := "0000000000000000000000000000" & "1000";
                    decode_trap_halt_control_bits := "00000000000000000000000000000" & '0' & '0' & '1';
                elsif instr_word_v(6 downto 0) = "1101111" then
                    decode_dispatch_class_bits := "0000000000000000000000000000" & "1001";
                    decode_trap_halt_control_bits := "00000000000000000000000000000" & '0' & '0' & '1';
                elsif instr_word_v(6 downto 0) = "0001111" then
                    decode_dispatch_class_bits := "0000000000000000000000000000" & "1010";
                    decode_trap_halt_control_bits := "00000000000000000000000000000" & '0' & '0' & '1';
                elsif instr_word_v(6 downto 0) = "0101111" then
                    decode_dispatch_class_bits := "0000000000000000000000000000" & "1110";
                    decode_trap_halt_control_bits := "00000000000000000000000000000" & '0' & '0' & '1';
                elsif instr_word_v(6 downto 0) = "1110011" then
                    decode_dispatch_class_bits := "0000000000000000000000000000" & "1011";
                    decode_trap_halt_control_bits := "00000000000000000000000000000" & '0' & '0' & '1';
                else
                    decode_trap_halt_control_bits := "00000000000000000000000000000" & '0' & '1' & '0';
                end if;
                case decode_dispatch_class_bits(3 downto 0) is
                    when "0001" | "0010" =>
                        decode_upper_immediate_bits := instr_word_v(31 downto 12) & "000000000000";
                    when "0011" =>
                        decode_writeback_bits := instr_word_v(31 downto 12) & instr_word_v(19 downto 15) & instr_word_v(6 downto 0);
                        decode_i_immediate_bits := "00000000000000000000" & instr_word_v(31 downto 20);
                        decode_execute_control_bits := "0000000000000000000000" & instr_word_v(25 downto 20) & instr_word_v(30 downto 30) & instr_word_v(14 downto 12);
                        if instr_word_v(14 downto 12) = "000" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "0000" & '0';
                        elsif instr_word_v(14 downto 12) = "001" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "0010" & '0';
                        elsif instr_word_v(14 downto 12) = "010" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "0011" & '0';
                        elsif instr_word_v(14 downto 12) = "011" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "0100" & '0';
                        elsif instr_word_v(14 downto 12) = "100" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "0101" & '0';
                        elsif instr_word_v(14 downto 12) = "101" and instr_word_v(30 downto 30) = "0" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "0110" & '0';
                        elsif instr_word_v(14 downto 12) = "101" and instr_word_v(30 downto 30) = "1" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "0111" & '0';
                        elsif instr_word_v(14 downto 12) = "110" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "1000" & '0';
                        elsif instr_word_v(14 downto 12) = "111" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "1001" & '0';
                        end if;
                    when "1100" =>
                        decode_i_immediate_bits := "00000000000000000000" & instr_word_v(31 downto 20);
                        decode_execute_control_bits := "0000000000000000000000" & instr_word_v(25 downto 20) & instr_word_v(30 downto 30) & instr_word_v(14 downto 12);
                        if instr_word_v(14 downto 12) = "000" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "0000" & '0';
                        elsif instr_word_v(14 downto 12) = "001" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "0010" & '0';
                        elsif instr_word_v(14 downto 12) = "101" and instr_word_v(30 downto 30) = "0" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "0110" & '0';
                        elsif instr_word_v(14 downto 12) = "101" and instr_word_v(30 downto 30) = "1" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "0111" & '0';
                        end if;
                    when "0100" =>
                        decode_execute_control_bits := "0000000000000000000000" & instr_word_v(25 downto 20) & instr_word_v(30 downto 30) & instr_word_v(14 downto 12);
                        if instr_word_v(14 downto 12) = "000" and instr_word_v(31 downto 25) = "0000000" then
                            decode_writeback_bits := instr_word_v(31 downto 12) & instr_word_v(24 downto 20) & instr_word_v(6 downto 0);
                        end if;
                        if instr_word_v(31 downto 25) = "0000001" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "1111" & '1';
                        elsif instr_word_v(14 downto 12) = "000" and instr_word_v(30 downto 30) = "0" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "0000" & '1';
                        elsif instr_word_v(14 downto 12) = "000" and instr_word_v(30 downto 30) = "1" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "0001" & '1';
                        elsif instr_word_v(14 downto 12) = "001" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "0010" & '1';
                        elsif instr_word_v(14 downto 12) = "010" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "0011" & '1';
                        elsif instr_word_v(14 downto 12) = "011" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "0100" & '1';
                        elsif instr_word_v(14 downto 12) = "100" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "0101" & '1';
                        elsif instr_word_v(14 downto 12) = "101" and instr_word_v(30 downto 30) = "0" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "0110" & '1';
                        elsif instr_word_v(14 downto 12) = "101" and instr_word_v(30 downto 30) = "1" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "0111" & '1';
                        elsif instr_word_v(14 downto 12) = "110" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "1000" & '1';
                        elsif instr_word_v(14 downto 12) = "111" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "1001" & '1';
                        end if;
                    when "1101" =>
                        decode_execute_control_bits := "0000000000000000000000" & instr_word_v(25 downto 20) & instr_word_v(30 downto 30) & instr_word_v(14 downto 12);
                        if instr_word_v(31 downto 25) = "0000001" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "1111" & '1';
                        elsif instr_word_v(14 downto 12) = "000" and instr_word_v(30 downto 30) = "0" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "0000" & '1';
                        elsif instr_word_v(14 downto 12) = "000" and instr_word_v(30 downto 30) = "1" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "0001" & '1';
                        elsif instr_word_v(14 downto 12) = "001" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "0010" & '1';
                        elsif instr_word_v(14 downto 12) = "101" and instr_word_v(30 downto 30) = "0" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "0110" & '1';
                        elsif instr_word_v(14 downto 12) = "101" and instr_word_v(30 downto 30) = "1" then
                            decode_execute_datapath_bits := "000000000000000000000000000" & "0111" & '1';
                        end if;
                    when "0101" =>
                        decode_i_immediate_bits := "00000000000000000000" & instr_word_v(31 downto 20);
                        decode_memory_access_control_bits := "00000000000000000000000000000" & instr_word_v(14 downto 12);
                    when "0110" =>
                        decode_store_immediate_bits := "00000000000000000000" & instr_word_v(31 downto 25) & instr_word_v(11 downto 7);
                        decode_memory_access_control_bits := "00000000000000000000000000000" & instr_word_v(14 downto 12);
                    when "0111" =>
                        decode_branch_immediate_bits := "00000000000000000000" & instr_word_v(31 downto 31) & instr_word_v(7 downto 7) & instr_word_v(30 downto 25) & instr_word_v(11 downto 8);
                        decode_execute_control_bits := "0000000000000000000000" & instr_word_v(25 downto 20) & instr_word_v(30 downto 30) & instr_word_v(14 downto 12);
                        if instr_word_v(14 downto 12) = "000" then
                            decode_branch_datapath_bits := "00000000000000000000000000000" & "000";
                        elsif instr_word_v(14 downto 12) = "001" then
                            decode_branch_datapath_bits := "00000000000000000000000000000" & "001";
                        elsif instr_word_v(14 downto 12) = "100" then
                            decode_branch_datapath_bits := "00000000000000000000000000000" & "010";
                        elsif instr_word_v(14 downto 12) = "101" then
                            decode_branch_datapath_bits := "00000000000000000000000000000" & "011";
                        elsif instr_word_v(14 downto 12) = "110" then
                            decode_branch_datapath_bits := "00000000000000000000000000000" & "100";
                        elsif instr_word_v(14 downto 12) = "111" then
                            decode_branch_datapath_bits := "00000000000000000000000000000" & "101";
                        end if;
                        decode_control_flow_datapath_bits := "00000000000000000000000000000" & '0' & "01";
                    when "1000" =>
                        decode_i_immediate_bits := "00000000000000000000" & instr_word_v(31 downto 20);
                        decode_control_flow_datapath_bits := "00000000000000000000000000000" & '1' & "10";
                    when "1001" =>
                        decode_jump_immediate_bits := "000000000000" & instr_word_v(31 downto 31) & instr_word_v(19 downto 12) & instr_word_v(20 downto 20) & instr_word_v(30 downto 21);
                        decode_control_flow_datapath_bits := "00000000000000000000000000000" & '1' & "11";
                    when others => null;
                end case;
                decode_writeback_rd_i := rd_i;
                imm_i := resize(signed(decode_i_immediate_bits(11 downto 0)), XLEN);
                imm_u := std_logic_vector(resize(signed(decode_upper_immediate_bits), XLEN));
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
                                pc_reg <= std_logic_vector(unsigned(pc_reg) + to_unsigned(instr_size_bytes, XLEN));
                            when "0010" =>
                                if rd_i /= 0 then
                                    regs(rd_i) <= std_logic_vector(signed(pc_reg) + signed(imm_u));
                                end if;
                                pc_reg <= std_logic_vector(unsigned(pc_reg) + to_unsigned(instr_size_bytes, XLEN));
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
                                pc_reg <= std_logic_vector(unsigned(pc_reg) + to_unsigned(instr_size_bytes, XLEN));
                            when "1100" =>
                                if decode_writeback_rd_i /= 0 then
                                    if XLEN = 64 and decode_execute_is_reg = '0' then
                                        case decode_execute_alu_op is
                                            when "0000" => regs(decode_writeback_rd_i) <= std_logic_vector(resize(signed(regs(rs1_i)(31 downto 0)) + signed(imm_i(31 downto 0)), XLEN));
                                            when "0010" => regs(decode_writeback_rd_i) <= std_logic_vector(resize(signed(std_logic_vector(shift_left(unsigned(regs(rs1_i)(31 downto 0)), to_integer(unsigned(instr_word_v(24 downto 20)))))), XLEN));
                                            when "0110" => regs(decode_writeback_rd_i) <= std_logic_vector(resize(signed(std_logic_vector(shift_right(unsigned(regs(rs1_i)(31 downto 0)), to_integer(unsigned(instr_word_v(24 downto 20)))))), XLEN));
                                            when "0111" => regs(decode_writeback_rd_i) <= std_logic_vector(resize(shift_right(signed(regs(rs1_i)(31 downto 0)), to_integer(unsigned(instr_word_v(24 downto 20)))), XLEN));
                                            when others => trap_reg <= '1';
                                        end case;
                                    else
                                        trap_reg <= '1';
                                    end if;
                                end if;
                                pc_reg <= std_logic_vector(unsigned(pc_reg) + to_unsigned(instr_size_bytes, XLEN));
                            when "0100" =>
                                if decode_writeback_rd_i /= 0 then
                                    if decode_execute_is_reg = '1' then
                                        if decode_execute_alu_op = "1111" then
                                            case instr_word_v(14 downto 12) is
                                                when "000" => regs(decode_writeback_rd_i) <= std_logic_vector(resize(signed(regs(rs1_i)) * signed(regs(rs2_i)), XLEN));
                                                when "100" =>
                                                    if regs(rs2_i) = x"0000000000000000" then
                                                        regs(decode_writeback_rd_i) <= (others => '1');
                                                    elsif regs(rs1_i) = x"8000000000000000" and regs(rs2_i) = x"FFFFFFFFFFFFFFFF" then
                                                        regs(decode_writeback_rd_i) <= regs(rs1_i);
                                                    else
                                                        regs(decode_writeback_rd_i) <= std_logic_vector(signed(regs(rs1_i)) / signed(regs(rs2_i)));
                                                    end if;
                                                when "101" =>
                                                    if regs(rs2_i) = x"0000000000000000" then
                                                        regs(decode_writeback_rd_i) <= (others => '1');
                                                    else
                                                        regs(decode_writeback_rd_i) <= std_logic_vector(unsigned(regs(rs1_i)) / unsigned(regs(rs2_i)));
                                                    end if;
                                                when "110" =>
                                                    if regs(rs2_i) = x"0000000000000000" then
                                                        regs(decode_writeback_rd_i) <= regs(rs1_i);
                                                    elsif regs(rs1_i) = x"8000000000000000" and regs(rs2_i) = x"FFFFFFFFFFFFFFFF" then
                                                        regs(decode_writeback_rd_i) <= (others => '0');
                                                    else
                                                        regs(decode_writeback_rd_i) <= std_logic_vector(signed(regs(rs1_i)) rem signed(regs(rs2_i)));
                                                    end if;
                                                when "111" =>
                                                    if regs(rs2_i) = x"0000000000000000" then
                                                        regs(decode_writeback_rd_i) <= regs(rs1_i);
                                                    else
                                                        regs(decode_writeback_rd_i) <= std_logic_vector(unsigned(regs(rs1_i)) rem unsigned(regs(rs2_i)));
                                                    end if;
                                                when others => trap_reg <= '1';
                                            end case;
                                        else
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
                                        end if;
                                    else
                                        trap_reg <= '1';
                                    end if;
                                end if;
                                pc_reg <= std_logic_vector(unsigned(pc_reg) + to_unsigned(instr_size_bytes, XLEN));
                            when "1101" =>
                                if decode_writeback_rd_i /= 0 then
                                    if XLEN = 64 and decode_execute_is_reg = '1' then
                                        if decode_execute_alu_op = "1111" then
                                            case instr_word_v(14 downto 12) is
                                                when "000" => regs(decode_writeback_rd_i) <= std_logic_vector(resize(signed(std_logic_vector(resize(signed(regs(rs1_i)(31 downto 0)) * signed(regs(rs2_i)(31 downto 0)), 32))), XLEN));
                                                when "100" =>
                                                    if regs(rs2_i)(31 downto 0) = x"00000000" then
                                                        regs(decode_writeback_rd_i) <= x"FFFFFFFFFFFFFFFF";
                                                    elsif regs(rs1_i)(31 downto 0) = x"80000000" and regs(rs2_i)(31 downto 0) = x"FFFFFFFF" then
                                                        regs(decode_writeback_rd_i) <= x"FFFFFFFF80000000";
                                                    else
                                                        regs(decode_writeback_rd_i) <= std_logic_vector(resize(signed(std_logic_vector(signed(regs(rs1_i)(31 downto 0)) / signed(regs(rs2_i)(31 downto 0)))), XLEN));
                                                    end if;
                                                when "101" =>
                                                    if regs(rs2_i)(31 downto 0) = x"00000000" then
                                                        regs(decode_writeback_rd_i) <= x"FFFFFFFFFFFFFFFF";
                                                    else
                                                        regs(decode_writeback_rd_i) <= std_logic_vector(resize(signed(std_logic_vector(unsigned(regs(rs1_i)(31 downto 0)) / unsigned(regs(rs2_i)(31 downto 0)))), XLEN));
                                                    end if;
                                                when "110" =>
                                                    if regs(rs2_i)(31 downto 0) = x"00000000" then
                                                        regs(decode_writeback_rd_i) <= std_logic_vector(resize(signed(regs(rs1_i)(31 downto 0)), XLEN));
                                                    elsif regs(rs1_i)(31 downto 0) = x"80000000" and regs(rs2_i)(31 downto 0) = x"FFFFFFFF" then
                                                        regs(decode_writeback_rd_i) <= (others => '0');
                                                    else
                                                        regs(decode_writeback_rd_i) <= std_logic_vector(resize(signed(std_logic_vector(signed(regs(rs1_i)(31 downto 0)) rem signed(regs(rs2_i)(31 downto 0)))), XLEN));
                                                    end if;
                                                when "111" =>
                                                    if regs(rs2_i)(31 downto 0) = x"00000000" then
                                                        regs(decode_writeback_rd_i) <= std_logic_vector(resize(signed(regs(rs1_i)(31 downto 0)), XLEN));
                                                    else
                                                        regs(decode_writeback_rd_i) <= std_logic_vector(resize(signed(std_logic_vector(unsigned(regs(rs1_i)(31 downto 0)) rem unsigned(regs(rs2_i)(31 downto 0)))), XLEN));
                                                    end if;
                                                when others => trap_reg <= '1';
                                            end case;
                                        else
                                        case decode_execute_alu_op is
                                            when "0000" => regs(decode_writeback_rd_i) <= std_logic_vector(resize(signed(regs(rs1_i)(31 downto 0)) + signed(regs(rs2_i)(31 downto 0)), XLEN));
                                            when "0001" => regs(decode_writeback_rd_i) <= std_logic_vector(resize(signed(regs(rs1_i)(31 downto 0)) - signed(regs(rs2_i)(31 downto 0)), XLEN));
                                            when "0010" => regs(decode_writeback_rd_i) <= std_logic_vector(resize(signed(std_logic_vector(shift_left(unsigned(regs(rs1_i)(31 downto 0)), to_integer(unsigned(regs(rs2_i)(4 downto 0)))))), XLEN));
                                            when "0110" => regs(decode_writeback_rd_i) <= std_logic_vector(resize(signed(std_logic_vector(shift_right(unsigned(regs(rs1_i)(31 downto 0)), to_integer(unsigned(regs(rs2_i)(4 downto 0)))))), XLEN));
                                            when "0111" => regs(decode_writeback_rd_i) <= std_logic_vector(resize(shift_right(signed(regs(rs1_i)(31 downto 0)), to_integer(unsigned(regs(rs2_i)(4 downto 0)))), XLEN));
                                            when others => trap_reg <= '1';
                                        end case;
                                        end if;
                                    else
                                        trap_reg <= '1';
                                    end if;
                                end if;
                                pc_reg <= std_logic_vector(unsigned(pc_reg) + to_unsigned(instr_size_bytes, XLEN));
                            when "0101" =>
                                addr_i := unsigned(signed(regs(rs1_i)) + imm_i);
                                sv39_translate_data(std_logic_vector(addr_i), csr_satp_reg, priv_mode_reg, '0', mmu_dmem_l2_pte, mmu_dmem_l1_pte, mmu_dmem_l0_pte, translated_addr_v, translated_fault_v);
                                dmem_addr_reg <= translated_addr_v;
                                dmem_re_reg <= '1';
                                if translated_fault_v = '1' then
                                    dmem_re_reg <= '0';
                                    csr_mepc_reg <= pc_reg;
                                    csr_mcause_reg <= std_logic_vector(to_unsigned(13, XLEN));
                                    csr_mtval_reg <= std_logic_vector(addr_i);
                                    csr_mstatus_reg(7) <= csr_mstatus_reg(3);
                                    csr_mstatus_reg(3) <= '0';
                                    csr_mstatus_reg(12 downto 11) <= priv_mode_reg;
                                    priv_mode_reg <= "11";
                                    pc_reg <= csr_mtvec_reg;
                                else
                                load_should_issue_v := false;
                                case decode_memory_funct3 is
                                    when "000" =>
                                        dmem_width_reg <= "00";
                                        load_should_issue_v := true;
                                    when "001" =>
                                        dmem_width_reg <= "01";
                                        if addr_i(0) = '1' then
                                            trap_reg <= '1';
                                        else
                                            load_should_issue_v := true;
                                        end if;
                                    when "010" =>
                                        dmem_width_reg <= "10";
                                        if addr_i(1 downto 0) /= "00" then
                                            trap_reg <= '1';
                                        else
                                            load_should_issue_v := true;
                                        end if;
                                    when "011" =>
                                        dmem_width_reg <= "11";
                                        if XLEN = 64 then
                                            if addr_i(2 downto 0) /= "000" then
                                                trap_reg <= '1';
                                            else
                                                load_should_issue_v := true;
                                            end if;
                                        else
                                            trap_reg <= '1';
                                        end if;
                                    when "100" =>
                                        dmem_width_reg <= "00";
                                        load_should_issue_v := true;
                                    when "101" =>
                                        dmem_width_reg <= "01";
                                        if addr_i(0) = '1' then
                                            trap_reg <= '1';
                                        else
                                            load_should_issue_v := true;
                                        end if;
                                    when "110" =>
                                        dmem_width_reg <= "10";
                                        if XLEN = 64 then
                                            if addr_i(1 downto 0) /= "00" then
                                                trap_reg <= '1';
                                            else
                                                load_should_issue_v := true;
                                            end if;
                                        else
                                            trap_reg <= '1';
                                        end if;
                                    when others => trap_reg <= '1';
                                end case;
                                if load_should_issue_v then
                                    load_issue_reg <= '1';
                                    load_pending_reg <= '1';
                                    load_pending_rd_reg <= rd_i;
                                    load_pending_addr_reg <= std_logic_vector(addr_i);
                                    load_pending_funct3_reg <= decode_memory_funct3;
                                    pc_reg <= std_logic_vector(unsigned(pc_reg) + to_unsigned(instr_size_bytes, XLEN));
                                else
                                    dmem_re_reg <= '0';
                                end if;
                                end if;
                            when "0110" =>
                                imm_i := resize(signed(decode_store_immediate_bits(11 downto 0)), XLEN);
                                addr_i := unsigned(signed(regs(rs1_i)) + imm_i);
                                sv39_translate_data(std_logic_vector(addr_i), csr_satp_reg, priv_mode_reg, '1', mmu_dmem_l2_pte, mmu_dmem_l1_pte, mmu_dmem_l0_pte, translated_addr_v, translated_fault_v);
                                dmem_addr_reg <= translated_addr_v;
                                if translated_fault_v = '1' then
                                    dmem_we_reg <= '0';
                                    dmem_wstrb_reg <= (others => '0');
                                    csr_mepc_reg <= pc_reg;
                                    csr_mcause_reg <= std_logic_vector(to_unsigned(15, XLEN));
                                    csr_mtval_reg <= std_logic_vector(addr_i);
                                    csr_mstatus_reg(7) <= csr_mstatus_reg(3);
                                    csr_mstatus_reg(3) <= '0';
                                    csr_mstatus_reg(12 downto 11) <= priv_mode_reg;
                                    priv_mode_reg <= "11";
                                    pc_reg <= csr_mtvec_reg;
                                else
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
                                        elsif XLEN = 64 then
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
                                        elsif XLEN = 64 then
                                            dmem_wdata_reg <= std_logic_vector(shift_left(unsigned(regs(rs2_i)), to_integer(unsigned(addr_i(2 downto 0))) * 8));
                                            dmem_wstrb_reg <= std_logic_vector(shift_left(to_unsigned(15, XLEN / 8), to_integer(unsigned(addr_i(2 downto 0)))));
                                            dmem_we_reg <= '1';
                                        elsif XLEN = 32 then
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
                                if trap_reg = '0' then
                                    reservation_valid_reg <= '0';
                                end if;
                                pc_reg <= std_logic_vector(unsigned(pc_reg) + to_unsigned(instr_size_bytes, XLEN));
                                end if;
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
                                    pc_reg <= std_logic_vector(unsigned(pc_reg) + to_unsigned(instr_size_bytes, XLEN));
                                end if;
                            when "1000" =>
                                addr_i := unsigned(signed(regs(rs1_i)) + imm_i);
                                addr_i(0) := '0';
                                if decode_writes_link = '1' and rd_i /= 0 then
                                    regs(rd_i) <= std_logic_vector(unsigned(pc_reg) + to_unsigned(instr_size_bytes, XLEN));
                                end if;
                                if decode_next_pc_op = "10" then
                                    pc_reg <= std_logic_vector(addr_i);
                                else
                                    trap_reg <= '1';
                                end if;
                            when "1001" =>
                                if decode_writes_link = '1' and rd_i /= 0 then
                                    regs(rd_i) <= std_logic_vector(unsigned(pc_reg) + to_unsigned(instr_size_bytes, XLEN));
                                end if;
                                if decode_next_pc_op = "11" then
                                    pc_reg <= std_logic_vector(unsigned(signed(pc_reg) + jump_i));
                                else
                                    trap_reg <= '1';
                                end if;
                            when "1110" =>
                                addr_i := unsigned(regs(rs1_i));
                                sv39_translate_data(std_logic_vector(addr_i), csr_satp_reg, priv_mode_reg, '1', mmu_dmem_l2_pte, mmu_dmem_l1_pte, mmu_dmem_l0_pte, translated_addr_v, translated_fault_v);
                                dmem_addr_reg <= translated_addr_v;
                                dmem_re_reg <= '1';
                                if translated_fault_v = '1' then
                                    dmem_re_reg <= '0';
                                    csr_mepc_reg <= pc_reg;
                                    csr_mcause_reg <= std_logic_vector(to_unsigned(15, XLEN));
                                    csr_mtval_reg <= std_logic_vector(addr_i);
                                    csr_mstatus_reg(7) <= csr_mstatus_reg(3);
                                    csr_mstatus_reg(3) <= '0';
                                    csr_mstatus_reg(12 downto 11) <= priv_mode_reg;
                                    priv_mode_reg <= "11";
                                    pc_reg <= csr_mtvec_reg;
                                else
                                    if instr_word_v(14 downto 12) = "010" then
                                        dmem_width_reg <= "10";
                                        if addr_i(1 downto 0) /= "00" then
                                            trap_reg <= '1';
                                        else
                                            amo_pending_reg <= '1';
                                        end if;
                                    elsif XLEN = 64 and instr_word_v(14 downto 12) = "011" then
                                        dmem_width_reg <= "11";
                                        if addr_i(2 downto 0) /= "000" then
                                            trap_reg <= '1';
                                        else
                                            amo_pending_reg <= '1';
                                        end if;
                                    else
                                        trap_reg <= '1';
                                    end if;
                                    if trap_reg = '0' then
                                        amo_pending_rd_reg <= rd_i;
                                        amo_pending_addr_reg <= translated_addr_v;
                                        amo_pending_funct3_reg <= instr_word_v(14 downto 12);
                                        amo_pending_funct5_reg <= instr_word_v(31 downto 27);
                                        amo_pending_rs2_value_reg <= regs(rs2_i);
                                    end if;
                                end if;
                            when "1010" =>
                                pc_reg <= std_logic_vector(unsigned(pc_reg) + to_unsigned(instr_size_bytes, XLEN));
                            when "1011" =>
                                if instr_word_v(14 downto 12) = "000" then
                                    if instr_word_v = x"00100073" then
                                        halt_reg <= '1';
                                    elsif instr_word_v = x"00000073" then
                                        if priv_mode_reg = "00" and csr_medeleg_reg(8) = '1' then
                                            csr_sepc_reg <= pc_reg;
                                            csr_scause_reg <= std_logic_vector(to_unsigned(8, XLEN));
                                            csr_stval_reg <= (others => '0');
                                            csr_mstatus_reg(5) <= csr_mstatus_reg(1);
                                            csr_mstatus_reg(1) <= '0';
                                            csr_mstatus_reg(8) <= '0';
                                            priv_mode_reg <= "01";
                                            pc_reg <= csr_stvec_reg;
                                        else
                                            csr_mepc_reg <= pc_reg;
                                            if priv_mode_reg = "00" then
                                                csr_mcause_reg <= std_logic_vector(to_unsigned(8, XLEN));
                                            elsif priv_mode_reg = "01" then
                                                csr_mcause_reg <= std_logic_vector(to_unsigned(9, XLEN));
                                            else
                                                csr_mcause_reg <= std_logic_vector(to_unsigned(11, XLEN));
                                            end if;
                                            csr_mtval_reg <= (others => '0');
                                            csr_mstatus_reg(7) <= csr_mstatus_reg(3);
                                            csr_mstatus_reg(3) <= '0';
                                            csr_mstatus_reg(12 downto 11) <= priv_mode_reg;
                                            priv_mode_reg <= "11";
                                            pc_reg <= csr_mtvec_reg;
                                        end if;
                                    elsif instr_word_v = x"30200073" then
                                        mret_mpp_v := csr_mstatus_reg(12 downto 11);
                                        csr_mstatus_reg(3) <= csr_mstatus_reg(7);
                                        csr_mstatus_reg(7) <= '1';
                                        csr_mstatus_reg(12 downto 11) <= "00";
                                        priv_mode_reg <= mret_mpp_v;
                                        pc_reg <= csr_mepc_reg;
                                    elsif instr_word_v = x"10200073" then
                                        csr_mstatus_reg(1) <= csr_mstatus_reg(5);
                                        csr_mstatus_reg(5) <= '1';
                                        if csr_mstatus_reg(8) = '1' then
                                            priv_mode_reg <= "01";
                                        else
                                            priv_mode_reg <= "00";
                                        end if;
                                        csr_mstatus_reg(8) <= '0';
                                        pc_reg <= csr_sepc_reg;
                                    elsif instr_word_v(31 downto 25) = "0001001" then
                                        pc_reg <= std_logic_vector(unsigned(pc_reg) + to_unsigned(instr_size_bytes, XLEN));
                                    else
                                        trap_reg <= '1';
                                    end if;
                                else
                                    csr_old_val := (others => '0');
                                    csr_new_val := (others => '0');
                                    case instr_word_v(31 downto 20) is
                                        when x"100" => csr_old_val := csr_mstatus_reg and x"00000000800DE133";
                                        when x"301" => csr_old_val := x"8000000000141105";
                                        when x"300" => csr_old_val := csr_mstatus_reg;
                                        when x"104" => csr_old_val := csr_mie_reg and csr_mideleg_reg;
                                        when x"304" => csr_old_val := csr_mie_reg;
                                        when x"105" => csr_old_val := csr_stvec_reg;
                                        when x"106" => csr_old_val := csr_scounteren_reg;
                                        when x"305" => csr_old_val := csr_mtvec_reg;
                                        when x"306" => csr_old_val := csr_mcounteren_reg;
                                        when x"140" => csr_old_val := csr_sscratch_reg;
                                        when x"340" => csr_old_val := csr_mscratch_reg;
                                        when x"141" => csr_old_val := csr_sepc_reg;
                                        when x"341" => csr_old_val := csr_mepc_reg;
                                        when x"142" => csr_old_val := csr_scause_reg;
                                        when x"342" => csr_old_val := csr_mcause_reg;
                                        when x"143" => csr_old_val := csr_stval_reg;
                                        when x"180" => csr_old_val := csr_satp_reg;
                                        when x"343" => csr_old_val := csr_mtval_reg;
                                        when x"144" =>
                                            csr_old_val := (others => '0');
                                            csr_old_val(9) := irq_external;
                                            csr_old_val(5) := irq_timer;
                                            csr_old_val(1) := irq_software;
                                            csr_old_val := csr_old_val and csr_mideleg_reg;
                                        when x"302" => csr_old_val := csr_medeleg_reg;
                                        when x"303" => csr_old_val := csr_mideleg_reg;
                                        when x"344" =>
                                            csr_old_val := (others => '0');
                                            csr_old_val(11) := irq_external;
                                            csr_old_val(7) := irq_timer;
                                            csr_old_val(3) := irq_software;
                                        when x"F11" => csr_old_val := (others => '0');
                                        when x"F12" => csr_old_val := (others => '0');
                                        when x"F13" => csr_old_val := (others => '0');
                                        when x"F14" => csr_old_val := (others => '0');
                                        when others => trap_reg <= '1';
                                    end case;
                                    if trap_reg = '0' then
                                        case instr_word_v(14 downto 12) is
                                            when "001" => csr_new_val := regs(rs1_i);
                                            when "010" =>
                                                if rs1_i = 0 then
                                                    csr_new_val := csr_old_val;
                                                else
                                                    csr_new_val := csr_old_val or regs(rs1_i);
                                                end if;
                                            when "011" =>
                                                if rs1_i = 0 then
                                                    csr_new_val := csr_old_val;
                                                else
                                                    csr_new_val := csr_old_val and (not regs(rs1_i));
                                                end if;
                                            when "101" => csr_new_val := std_logic_vector(to_unsigned(rs1_i, XLEN));
                                            when "110" =>
                                                if rs1_i = 0 then
                                                    csr_new_val := csr_old_val;
                                                else
                                                    csr_new_val := csr_old_val or std_logic_vector(to_unsigned(rs1_i, XLEN));
                                                end if;
                                            when "111" =>
                                                if rs1_i = 0 then
                                                    csr_new_val := csr_old_val;
                                                else
                                                    csr_new_val := csr_old_val and (not std_logic_vector(to_unsigned(rs1_i, XLEN)));
                                                end if;
                                            when others => trap_reg <= '1';
                                        end case;
                                    end if;
                                    if trap_reg = '0' then
                                        if rd_i /= 0 then
                                            regs(rd_i) <= csr_old_val;
                                        end if;
                                        case instr_word_v(14 downto 12) is
                                            when "001" | "010" | "011" | "101" | "110" | "111" =>
                                                case instr_word_v(31 downto 20) is
                                                    when x"100" => csr_mstatus_reg <= (csr_mstatus_reg and (not x"00000000800DE133")) or (csr_new_val and x"00000000800DE133");
                                                    when x"300" => csr_mstatus_reg <= csr_new_val;
                                                    when x"104" => csr_mie_reg <= (csr_mie_reg and (not csr_mideleg_reg)) or (csr_new_val and csr_mideleg_reg);
                                                    when x"304" => csr_mie_reg <= csr_new_val;
                                                    when x"105" => csr_stvec_reg <= csr_new_val;
                                                    when x"106" => csr_scounteren_reg <= csr_new_val;
                                                    when x"305" => csr_mtvec_reg <= csr_new_val;
                                                    when x"306" => csr_mcounteren_reg <= csr_new_val;
                                                    when x"140" => csr_sscratch_reg <= csr_new_val;
                                                    when x"340" => csr_mscratch_reg <= csr_new_val;
                                                    when x"141" => csr_sepc_reg <= csr_new_val;
                                                    when x"341" => csr_mepc_reg <= csr_new_val;
                                                    when x"142" => csr_scause_reg <= csr_new_val;
                                                    when x"342" => csr_mcause_reg <= csr_new_val;
                                                    when x"143" => csr_stval_reg <= csr_new_val;
                                                    when x"180" => csr_satp_reg <= csr_new_val;
                                                    when x"343" => csr_mtval_reg <= csr_new_val;
                                                    when x"302" => csr_medeleg_reg <= csr_new_val;
                                                    when x"303" => csr_mideleg_reg <= csr_new_val;
                                                    when others => null;
                                                end case;
                                                pc_reg <= std_logic_vector(unsigned(pc_reg) + to_unsigned(instr_size_bytes, XLEN));
                                            when others => trap_reg <= '1';
                                        end case;
                                    end if;
                                end if;
                            when others =>
                                trap_reg <= '1';
                        end case;
                    elsif decode_should_halt = '1' then
                        halt_reg <= '1';
                    elsif decode_should_trap = '1' then
                        trap_reg <= '1';
                    end if;
                    semi_phase_reg <= 0;
                    regs(0) <= (others => '0');
                end if;
                end if;
            end if;
        end if;
    end process;
end architecture rtl;
