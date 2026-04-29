library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use work.test_program.all;
use work.simple_rv64i_core_pkg.all;

entity tb_generated_rv64_sv39 is
    generic (
        MAX_CYCLES : integer := 200000
    );
end entity tb_generated_rv64_sv39;

architecture sim of tb_generated_rv64_sv39 is
    constant CLK_PERIOD : time := 10 ns;
    constant MEM_WORDS  : integer := 8192;
    constant PASS_ADDR  : integer := 16#100#;
    constant FAIL_ADDR  : integer := 16#108#;
    constant TRAP_CAUSE_ADDR : integer := 16#110#;
    constant TRAP_TVAL_ADDR  : integer := 16#118#;
    constant MMU_L2_PTE : std_logic_vector(63 downto 0) := x"0000000000400001";
    constant MMU_L1_PTE : std_logic_vector(63 downto 0) := x"0000000000800001";
    constant MMU_L0_PTE : std_logic_vector(63 downto 0) := x"00000000000000C7";

    signal clk        : std_logic := '0';
    signal reset_n    : std_logic := '0';
    signal imem_addr  : std_logic_vector(63 downto 0) := (others => '0');
    signal imem_data  : std_logic_vector(31 downto 0) := (others => '0');
    signal dmem_addr  : std_logic_vector(63 downto 0) := (others => '0');
    signal dmem_wdata : std_logic_vector(63 downto 0) := (others => '0');
    signal dmem_rdata : std_logic_vector(63 downto 0) := (others => '0');
    signal dmem_we    : std_logic := '0';
    signal dmem_re    : std_logic := '0';
    signal dmem_width : std_logic_vector(1 downto 0) := (others => '0');
    signal dmem_wstrb : std_logic_vector(7 downto 0) := (others => '0');
    signal irq_software : std_logic := '0';
    signal irq_timer    : std_logic := '0';
    signal irq_external : std_logic := '0';
    signal debug_priv_mode : std_logic_vector(1 downto 0) := (others => '0');
    signal debug_pc   : std_logic_vector(63 downto 0) := (others => '0');
    signal trap       : std_logic := '0';
    signal halt       : std_logic := '0';

    type mem_t is array (0 to MEM_WORDS - 1) of std_logic_vector(63 downto 0);

    function init_mem return mem_t is
        variable m : mem_t := (others => x"0000001300000013");
        variable word_idx : integer;
        variable byte_idx : integer;
        variable current_word : std_logic_vector(63 downto 0);
    begin
        for i in 0 to PROGRAM_SIZE_BYTES - 1 loop
            word_idx := i / 8;
            byte_idx := i mod 8;
            current_word := m(word_idx);
            current_word((byte_idx * 8) + 7 downto byte_idx * 8) := PROGRAM_BYTES(i);
            m(word_idx) := current_word;
        end loop;
        return m;
    end function;

    function safe_index(bits : std_logic_vector) return integer is
    begin
        for i in bits'range loop
            if bits(i) /= '0' and bits(i) /= '1' then
                return 0;
            end if;
        end loop;
        return to_integer(unsigned(bits));
    end function;

    function word32_to_report_int(word_val : std_logic_vector(31 downto 0)) return integer is
    begin
        if word_val(31) = '1' then
            return -1;
        end if;
        return safe_index(word_val(30 downto 0));
    end function;

    function dmem_word_index(addr : std_logic_vector(63 downto 0)) return integer is
    begin
        if addr(63 downto 16) /= (63 downto 16 => '0') then
            return MEM_WORDS;
        end if;
        return safe_index(addr(15 downto 3));
    end function;

    signal mem : mem_t := init_mem;
    signal done : boolean := false;
    signal last_write_word_idx : integer := -1;
    signal last_write_low32 : std_logic_vector(31 downto 0) := (others => '0');
    signal last_write_high32 : std_logic_vector(31 downto 0) := (others => '0');
    signal last_we_addr_low16 : integer := -1;
    signal last_we_addr_high32 : integer := -1;
    signal last_re_addr_low16 : integer := -1;
    signal last_re_addr_high32 : integer := -1;
begin
    u_cpu : entity work.simple_rv64gc_core
        port map (
            clk        => clk,
            reset_n    => reset_n,
            imem_addr  => imem_addr,
            imem_rdata => imem_data,
            dmem_addr  => dmem_addr,
            dmem_wdata => dmem_wdata,
            dmem_rdata => dmem_rdata,
            dmem_we    => dmem_we,
            dmem_re    => dmem_re,
            dmem_width => dmem_width,
            dmem_wstrb => dmem_wstrb,
            irq_software => irq_software,
            irq_timer  => irq_timer,
            irq_external => irq_external,
            mmu_dmem_l2_pte => MMU_L2_PTE,
            mmu_dmem_l1_pte => MMU_L1_PTE,
            mmu_dmem_l0_pte => MMU_L0_PTE,
            debug_priv_mode => debug_priv_mode,
            debug_pc   => debug_pc,
            trap       => trap,
            halt       => halt
        );

    clk <= not clk after CLK_PERIOD / 2 when not done else '0';

    imem_data <= mem(safe_index(imem_addr(15 downto 3)))(31 downto 0)
        when safe_index(imem_addr(15 downto 3)) < MEM_WORDS and imem_addr(2) = '0'
        else mem(safe_index(imem_addr(15 downto 3)))(63 downto 32)
        when safe_index(imem_addr(15 downto 3)) < MEM_WORDS
        else x"00000013";

    process(clk)
        variable word_idx : integer;
        variable current_word : std_logic_vector(63 downto 0);
    begin
        if rising_edge(clk) then
            if dmem_we = '1' then
                last_we_addr_low16 <= safe_index(dmem_addr(15 downto 0));
                last_we_addr_high32 <= safe_index(dmem_addr(63 downto 32));
                word_idx := dmem_word_index(dmem_addr);
                if word_idx < MEM_WORDS then
                    current_word := mem(word_idx);
                    for i in 0 to 7 loop
                        if dmem_wstrb(i) = '1' then
                            current_word((i * 8) + 7 downto i * 8) := dmem_wdata((i * 8) + 7 downto i * 8);
                        end if;
                    end loop;
                    mem(word_idx) <= current_word;
                    last_write_word_idx <= word_idx;
                    last_write_low32 <= current_word(31 downto 0);
                    last_write_high32 <= current_word(63 downto 32);
                end if;
            end if;
            if dmem_re = '1' then
                last_re_addr_low16 <= safe_index(dmem_addr(15 downto 0));
                last_re_addr_high32 <= safe_index(dmem_addr(63 downto 32));
            end if;
        end if;
    end process;

    dmem_rdata <= mem(dmem_word_index(dmem_addr))
        when dmem_word_index(dmem_addr) < MEM_WORDS
        else (others => '0');

    process
        variable cycles : integer := 0;
        variable pass_value : integer;
        variable fail_value : integer;
        variable trap_cause_value : integer;
        variable trap_tval_value : integer;
    begin
        reset_n <= '0';
        wait for CLK_PERIOD * 5;
        reset_n <= '1';

        while halt = '0' and trap = '0' and cycles < MAX_CYCLES loop
            wait for CLK_PERIOD;
            cycles := cycles + 1;
        end loop;

        pass_value := word32_to_report_int(mem(PASS_ADDR / 8)(31 downto 0));
        fail_value := word32_to_report_int(mem(FAIL_ADDR / 8)(31 downto 0));
        trap_cause_value := word32_to_report_int(mem(TRAP_CAUSE_ADDR / 8)(31 downto 0));
        trap_tval_value := word32_to_report_int(mem(TRAP_TVAL_ADDR / 8)(31 downto 0));
        report "CYCLES: " & integer'image(cycles);
        report "PASS_WORD: " & integer'image(pass_value);
        report "FAIL_WORD: " & integer'image(fail_value);
        report "TRAP_CAUSE_WORD: " & integer'image(trap_cause_value);
        report "TRAP_TVAL_WORD: " & integer'image(trap_tval_value);
        report "FINAL_PRIV_MODE: " & integer'image(safe_index(debug_priv_mode));
        report "FINAL_PC_LOW16: " & integer'image(safe_index(debug_pc(15 downto 0)));
        report "LAST_WE_ADDR_LOW16: " & integer'image(last_we_addr_low16);
        report "LAST_WE_ADDR_HIGH32: " & integer'image(last_we_addr_high32);
        report "LAST_RE_ADDR_LOW16: " & integer'image(last_re_addr_low16);
        report "LAST_RE_ADDR_HIGH32: " & integer'image(last_re_addr_high32);
        report "LAST_WRITE_WORD_IDX: " & integer'image(last_write_word_idx);
        report "LAST_WRITE_LOW32: " & integer'image(word32_to_report_int(last_write_low32));
        report "LAST_WRITE_HIGH32: " & integer'image(word32_to_report_int(last_write_high32));
        if halt = '1' and pass_value = 42 and fail_value = 42 then
            report "GENERATED_RV64_SV39: PASS";
        else
            report "GENERATED_RV64_SV39: FAIL";
        end if;
        done <= true;
        wait;
    end process;
end architecture sim;
