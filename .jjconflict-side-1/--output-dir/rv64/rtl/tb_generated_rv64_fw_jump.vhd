library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use work.test_program.all;
use work.simple_rv64i_core_pkg.all;

entity tb_generated_rv64_fw_jump is
    generic (
        MAX_CYCLES : integer := 300000
    );
end entity tb_generated_rv64_fw_jump;

architecture sim of tb_generated_rv64_fw_jump is
    constant CLK_PERIOD : time := 10 ns;
    constant MEM_WORDS  : integer := 270000;
    constant PASS_ADDR_BITS : std_logic_vector(63 downto 0) := x"0000000080200100";
    constant A0_ADDR_BITS   : std_logic_vector(63 downto 0) := x"0000000080200110";
    constant A1_ADDR_BITS   : std_logic_vector(63 downto 0) := x"0000000080200118";
    constant UART_ADDR  : std_logic_vector(63 downto 0) := x"0000000010000000";
    constant UART_MAGIC : std_logic_vector(31 downto 0) := x"544F4253";
    constant BOOT_A0    : std_logic_vector(63 downto 0) := x"0000000000000000";
    constant BOOT_A1    : std_logic_vector(63 downto 0) := x"0000000088000000";

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
    signal debug_last_load_value : std_logic_vector(63 downto 0) := (others => '0');
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


    function fetch_imem_word(mem_state : mem_t; addr : std_logic_vector(63 downto 0)) return std_logic_vector is
        variable idx : integer;
        variable next_idx : integer;
        variable current_word : std_logic_vector(63 downto 0);
        variable next_word : std_logic_vector(63 downto 0) := x"0000001300000013";
        variable result : std_logic_vector(31 downto 0) := x"00000013";
    begin
        idx := mem_index(addr);
        if idx >= MEM_WORDS then
            return result;
        end if;
        current_word := mem_state(idx);
        case addr(2 downto 1) is
            when "00" => result := current_word(31 downto 0);
            when "01" => result := current_word(47 downto 16);
            when "10" => result := current_word(63 downto 32);
            when others =>
                next_idx := idx + 1;
                if next_idx < MEM_WORDS then
                    next_word := mem_state(next_idx);
                end if;
                result(15 downto 0) := current_word(63 downto 48);
                result(31 downto 16) := next_word(15 downto 0);
        end case;
        return result;
    end function;

    signal mem : mem_t := init_mem;
    signal uart_word : std_logic_vector(31 downto 0) := (others => '0');
    signal uart_count : integer range 0 to 4 := 0;
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
            debug_last_load_value => debug_last_load_value,
            debug_pc   => debug_pc,
            trap       => trap,
            halt       => halt
        );

    clk <= not clk after CLK_PERIOD / 2 when not done else '0';

    imem_data <= fetch_imem_word(mem, imem_addr);

    process(clk)
        variable word_idx : integer;
        variable current_word : std_logic_vector(63 downto 0);
    begin
        if rising_edge(clk) then
            if dmem_we = '1' and dmem_addr = UART_ADDR and dmem_wstrb(0) = '1' then
                if uart_count < 4 then
                    uart_word((uart_count * 8) + 7 downto uart_count * 8) <= dmem_wdata(7 downto 0);
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
        report "CYCLES: " & integer'image(cycles);
        report "PASS_WORD: " & integer'image(pass_value);
        report "A0_LOW32: " & integer'image(a0_low_value);
        report "A1_LOW32: " & integer'image(a1_low_value);
        report "A1_HIGH32: " & integer'image(a1_high_value);
        report "UART_BYTES_LOW32: " & integer'image(word32_to_report_int(uart_word));
        report "PRIV_MODE: " & integer'image(safe_index(debug_priv_mode));
        report "PC_LOW32: " & integer'image(word32_to_report_int(debug_pc(31 downto 0)));
        if halt = '1' and pass_value = 42 and uart_word = UART_MAGIC and mem(mem_index(A0_ADDR_BITS)) = BOOT_A0 and mem(mem_index(A1_ADDR_BITS)) = BOOT_A1 and debug_priv_mode = "01" then
            report "GENERATED_RV64_FW_JUMP: PASS";
        else
            report "GENERATED_RV64_FW_JUMP: FAIL";
        end if;
        done <= true;
        wait;
    end process;
end architecture sim;
