library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use work.test_program.all;
use work.simple_rv64i_core_pkg.all;

entity tb_generated_rv64_boot_banner is
    generic (
        MAX_CYCLES : integer := 300000
    );
end entity tb_generated_rv64_boot_banner;

architecture sim of tb_generated_rv64_boot_banner is
    constant CLK_PERIOD : time := 10 ns;
    constant MEM_WORDS  : integer := 270000;
    constant PASS_ADDR_BITS : std_logic_vector(63 downto 0) := x"0000000080200100";
    constant A0_ADDR_BITS   : std_logic_vector(63 downto 0) := x"0000000080200110";
    constant A1_ADDR_BITS   : std_logic_vector(63 downto 0) := x"0000000080200118";
    constant UART_ADDR      : std_logic_vector(63 downto 0) := x"0000000010000000";
    constant BOOT_A0        : std_logic_vector(63 downto 0) := x"0000000000000000";
    constant BOOT_A1        : std_logic_vector(63 downto 0) := x"0000000088000000";
    constant BSS0_ADDR_BITS : std_logic_vector(63 downto 0) := x"0000000080202000";
    constant BSS1_ADDR_BITS : std_logic_vector(63 downto 0) := x"0000000080202008";
    constant BSS2_ADDR_BITS : std_logic_vector(63 downto 0) := x"0000000080202010";
    constant BSS3_ADDR_BITS : std_logic_vector(63 downto 0) := x"0000000080202018";
    constant UART_EXPECTED_COUNT : integer := 15;

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
    type uart_capture_t is array (0 to UART_EXPECTED_COUNT - 1) of std_logic_vector(7 downto 0);

    function init_mem return mem_t is
        variable m : mem_t := (others => x"0000001300000013");
        variable word_idx : integer;
        variable byte_idx : integer;
        variable current_word : std_logic_vector(63 downto 0);
    begin
        for i in 0 to FW_SIZE_BYTES - 1 loop
            word_idx := i / 8;
            byte_idx := i mod 8;
            if word_idx < MEM_WORDS then
                current_word := m(word_idx);
                current_word((byte_idx * 8) + 7 downto byte_idx * 8) := FW_BYTES(i);
                m(word_idx) := current_word;
            end if;
        end loop;
        for i in 0 to PAYLOAD_SIZE_BYTES - 1 loop
            word_idx := (16#200000# + i) / 8;
            byte_idx := (16#200000# + i) mod 8;
            if word_idx < MEM_WORDS then
                current_word := m(word_idx);
                current_word((byte_idx * 8) + 7 downto byte_idx * 8) := PAYLOAD_BYTES(i);
                m(word_idx) := current_word;
            end if;
        end loop;
        m(16#202000# / 8) := x"1111111111111111";
        m(16#202008# / 8) := x"2222222222222222";
        m(16#202010# / 8) := x"3333333333333333";
        m(16#202018# / 8) := x"4444444444444444";
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

    function mem_index(addr : std_logic_vector(63 downto 0)) return integer is
    begin
        return safe_index(addr(21 downto 3));
    end function;

    function uart_matches_banner(bytes : uart_capture_t) return boolean is
    begin
        return bytes(0) = x"53" and
            bytes(1) = x"69" and
            bytes(2) = x"6D" and
            bytes(3) = x"70" and
            bytes(4) = x"6C" and
            bytes(5) = x"65" and
            bytes(6) = x"4F" and
            bytes(7) = x"53" and
            bytes(8) = x"20" and
            bytes(9) = x"52" and
            bytes(10) = x"56" and
            bytes(11) = x"36" and
            bytes(12) = x"34" and
            bytes(13) = x"0D" and
            bytes(14) = x"0A";
    end function;

    signal mem : mem_t := init_mem;
    signal uart_bytes : uart_capture_t := (others => (others => '0'));
    signal uart_count : integer range 0 to UART_EXPECTED_COUNT := 0;
    signal done : boolean := false;
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
            mmu_dmem_l2_pte => (others => '0'),
            mmu_dmem_l1_pte => (others => '0'),
            mmu_dmem_l0_pte => (others => '0'),
            debug_priv_mode => debug_priv_mode,
            debug_last_load_value => open,
            debug_pc   => debug_pc,
            trap       => trap,
            halt       => halt
        );

    clk <= not clk after CLK_PERIOD / 2 when not done else '0';

    imem_data <= mem(mem_index(imem_addr))(31 downto 0)
        when mem_index(imem_addr) < MEM_WORDS and imem_addr(2) = '0'
        else mem(mem_index(imem_addr))(63 downto 32)
        when mem_index(imem_addr) < MEM_WORDS
        else x"00000013";

    process(clk)
        variable word_idx : integer;
        variable current_word : std_logic_vector(63 downto 0);
    begin
        if rising_edge(clk) then
            if dmem_we = '1' and dmem_addr = UART_ADDR and dmem_wstrb(0) = '1' then
                if uart_count < UART_EXPECTED_COUNT then
                    uart_bytes(uart_count) <= dmem_wdata(7 downto 0);
                    uart_count <= uart_count + 1;
                end if;
            elsif dmem_we = '1' then
                word_idx := mem_index(dmem_addr);
                if word_idx < MEM_WORDS then
                    current_word := mem(word_idx);
                    for i in 0 to 7 loop
                        if dmem_wstrb(i) = '1' then
                            current_word((i * 8) + 7 downto i * 8) := dmem_wdata((i * 8) + 7 downto i * 8);
                        end if;
                    end loop;
                    mem(word_idx) <= current_word;
                end if;
            end if;
        end if;
    end process;

    dmem_rdata <= mem(mem_index(dmem_addr))
        when mem_index(dmem_addr) < MEM_WORDS
        else (others => '0');

    process
        variable cycles : integer := 0;
        variable pass_value : integer;
        variable a0_low_value : integer;
        variable a1_low_value : integer;
        variable a1_high_value : integer;
        variable bss_cleared : boolean;
        variable uart_ok : boolean;
    begin
        reset_n <= '0';
        wait for CLK_PERIOD * 5;
        reset_n <= '1';

        while halt = '0' and trap = '0' and cycles < MAX_CYCLES loop
            wait for CLK_PERIOD;
            cycles := cycles + 1;
        end loop;

        pass_value := word32_to_report_int(mem(mem_index(PASS_ADDR_BITS))(31 downto 0));
        a0_low_value := word32_to_report_int(mem(mem_index(A0_ADDR_BITS))(31 downto 0));
        a1_low_value := word32_to_report_int(mem(mem_index(A1_ADDR_BITS))(31 downto 0));
        a1_high_value := word32_to_report_int(mem(mem_index(A1_ADDR_BITS))(63 downto 32));
        bss_cleared := mem(mem_index(BSS0_ADDR_BITS)) = x"0000000000000000" and
            mem(mem_index(BSS1_ADDR_BITS)) = x"0000000000000000" and
            mem(mem_index(BSS2_ADDR_BITS)) = x"0000000000000000" and
            mem(mem_index(BSS3_ADDR_BITS)) = x"0000000000000000";
        uart_ok := uart_count = UART_EXPECTED_COUNT and uart_matches_banner(uart_bytes);

        report "CYCLES: " & integer'image(cycles);
        report "PASS_WORD: " & integer'image(pass_value);
        report "A0_LOW32: " & integer'image(a0_low_value);
        report "A1_LOW32: " & integer'image(a1_low_value);
        report "A1_HIGH32: " & integer'image(a1_high_value);
        report "UART_COUNT: " & integer'image(uart_count);
        report "BSS_CLEARED: " & boolean'image(bss_cleared);
        report "PRIV_MODE: " & integer'image(safe_index(debug_priv_mode));
        report "PC_LOW32: " & integer'image(word32_to_report_int(debug_pc(31 downto 0)));
        if halt = '1' and pass_value = 42 and mem(mem_index(A0_ADDR_BITS)) = BOOT_A0 and mem(mem_index(A1_ADDR_BITS)) = BOOT_A1 and debug_priv_mode = "01" and uart_ok and bss_cleared then
            report "GENERATED_RV64_BOOT_BANNER: PASS";
        else
            report "GENERATED_RV64_BOOT_BANNER: FAIL";
        end if;
        done <= true;
        wait;
    end process;
end architecture sim;
