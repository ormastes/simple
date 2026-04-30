library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use work.test_program.all;
use work.simple_rv64i_core_pkg.all;

entity tb_generated_rv64_boot_info_real_dtb is
    generic (
        MAX_CYCLES : integer := 300000
    );
end entity tb_generated_rv64_boot_info_real_dtb;

architecture sim of tb_generated_rv64_boot_info_real_dtb is
    constant CLK_PERIOD : time := 10 ns;
    constant MEM_WORDS  : integer := 270000;
    constant PASS_ADDR_BITS      : std_logic_vector(63 downto 0) := x"0000000080200400";
    constant A0_ADDR_BITS        : std_logic_vector(63 downto 0) := x"0000000080200410";
    constant A1_ADDR_BITS        : std_logic_vector(63 downto 0) := x"0000000080200418";
    constant DTB_VALID_ADDR_BITS : std_logic_vector(63 downto 0) := x"0000000080200420";
    constant RAM_BASE_ADDR_BITS  : std_logic_vector(63 downto 0) := x"0000000080200428";
    constant RAM_SIZE_ADDR_BITS  : std_logic_vector(63 downto 0) := x"0000000080200430";
    constant UART_ADDR           : std_logic_vector(63 downto 0) := x"0000000010000000";
    constant UART_MAGIC          : std_logic_vector(31 downto 0) := x"52425444";
    constant BOOT_A0             : std_logic_vector(63 downto 0) := x"0000000000000000";
    constant BOOT_A1             : std_logic_vector(63 downto 0) := x"0000000088000000";
    constant DTB_BASE            : std_logic_vector(63 downto 0) := x"0000000088000000";
    constant DTB_SIZE_BYTES      : integer := 128;
    constant DTB_RAM_BASE        : std_logic_vector(63 downto 0) := x"0000000080000000";
    constant DTB_RAM_SIZE        : std_logic_vector(63 downto 0) := x"0000000008000000";

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
    constant DTB_BYTES : byte_array_t(0 to DTB_SIZE_BYTES - 1) := (
        x"D0", x"0D", x"FE", x"ED",
        x"00", x"00", x"00", x"80",
        x"00", x"00", x"00", x"38",
        x"00", x"00", x"00", x"7C",
        x"00", x"00", x"00", x"28",
        x"00", x"00", x"00", x"11",
        x"00", x"00", x"00", x"10",
        x"00", x"00", x"00", x"00",
        x"00", x"00", x"00", x"04",
        x"00", x"00", x"00", x"44",
        x"00", x"00", x"00", x"00", x"00", x"00", x"00", x"00",
        x"00", x"00", x"00", x"00", x"00", x"00", x"00", x"00",
        x"00", x"00", x"00", x"01",
        x"00", x"00", x"00", x"00",
        x"00", x"00", x"00", x"01",
        x"6D", x"65", x"6D", x"6F", x"72", x"79", x"40", x"38",
        x"30", x"30", x"30", x"30", x"30", x"30", x"30", x"00",
        x"00", x"00", x"00", x"03",
        x"00", x"00", x"00", x"10",
        x"00", x"00", x"00", x"00",
        x"00", x"00", x"00", x"00", x"80", x"00", x"00", x"00",
        x"00", x"00", x"00", x"00", x"08", x"00", x"00", x"00",
        x"00", x"00", x"00", x"02",
        x"00", x"00", x"00", x"02",
        x"00", x"00", x"00", x"09",
        x"72", x"65", x"67", x"00"
    );

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

    function hex_char(nibble : std_logic_vector(3 downto 0)) return character is
        variable idx : integer;
    begin
        idx := safe_index(nibble);
        case idx is
            when 0 => return '0';
            when 1 => return '1';
            when 2 => return '2';
            when 3 => return '3';
            when 4 => return '4';
            when 5 => return '5';
            when 6 => return '6';
            when 7 => return '7';
            when 8 => return '8';
            when 9 => return '9';
            when 10 => return 'A';
            when 11 => return 'B';
            when 12 => return 'C';
            when 13 => return 'D';
            when 14 => return 'E';
            when others => return 'F';
        end case;
    end function;

    function hex32(bits : std_logic_vector(31 downto 0)) return string is
        variable result : string(1 to 8);
    begin
        for i in 0 to 7 loop
            result(i + 1) := hex_char(bits(31 - (i * 4) downto 28 - (i * 4)));
        end loop;
        return result;
    end function;

    function mem_index(addr : std_logic_vector(63 downto 0)) return integer is
    begin
        return safe_index(addr(21 downto 3));
    end function;

    function dtb_word(addr : std_logic_vector(63 downto 0)) return std_logic_vector is
        variable result : std_logic_vector(63 downto 0) := (others => '0');
        variable base_offset : integer;
        variable byte_offset : integer;
    begin
        base_offset := safe_index(addr(6 downto 3)) * 8;
        for i in 0 to 7 loop
            byte_offset := base_offset + i;
            if byte_offset < DTB_SIZE_BYTES then
                result((i * 8) + 7 downto i * 8) := DTB_BYTES(byte_offset);
            end if;
        end loop;
        return result;
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
    signal dtb_probe_seen : boolean := false;
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

    imem_data <= fetch_imem_word(mem, imem_addr);

    process(clk)
        variable word_idx : integer;
        variable current_word : std_logic_vector(63 downto 0);
    begin
        if rising_edge(clk) then
            if dmem_re = '1' and unsigned(dmem_addr) >= unsigned(DTB_BASE) and unsigned(dmem_addr) < unsigned(DTB_BASE) + to_unsigned(DTB_SIZE_BYTES, 64) then
                dtb_probe_seen <= true;
            end if;

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

    dmem_rdata <= dtb_word(dmem_addr)
        when unsigned(dmem_addr) >= unsigned(DTB_BASE) and unsigned(dmem_addr) < unsigned(DTB_BASE) + to_unsigned(DTB_SIZE_BYTES, 64)
        else mem(mem_index(dmem_addr))
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
        report "DTB_VALID_LOW32: " & integer'image(word32_to_report_int(mem(mem_index(DTB_VALID_ADDR_BITS))(31 downto 0)));
        report "RAM_BASE_HEX32: " & hex32(mem(mem_index(RAM_BASE_ADDR_BITS))(31 downto 0));
        report "RAM_SIZE_HEX32: " & hex32(mem(mem_index(RAM_SIZE_ADDR_BITS))(31 downto 0));
        report "DTB_PROBE_SEEN: " & boolean'image(dtb_probe_seen);
        report "UART_BYTES_LOW32: " & integer'image(word32_to_report_int(uart_word));
        report "PRIV_MODE: " & integer'image(safe_index(debug_priv_mode));
        report "PC_LOW32: " & integer'image(word32_to_report_int(debug_pc(31 downto 0)));
        if halt = '1' and pass_value = 42 and mem(mem_index(A0_ADDR_BITS)) = BOOT_A0 and mem(mem_index(A1_ADDR_BITS)) = BOOT_A1 and mem(mem_index(DTB_VALID_ADDR_BITS)) = x"0000000000000001" and mem(mem_index(RAM_BASE_ADDR_BITS)) = DTB_RAM_BASE and mem(mem_index(RAM_SIZE_ADDR_BITS)) = DTB_RAM_SIZE and uart_word = UART_MAGIC and debug_priv_mode = "01" and dtb_probe_seen then
            report "GENERATED_RV64_BOOT_INFO_REAL_DTB: PASS";
        else
            report "GENERATED_RV64_BOOT_INFO_REAL_DTB: FAIL";
        end if;
        done <= true;
        wait;
    end process;
end architecture sim;
