library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use std.textio.all;
use work.test_program.all;
use work.simple_rv64i_core_pkg.all;

entity tb_generated_rv64_boot_info_dtb is
    generic (
        MAX_CYCLES : integer := 300000
    );
end entity tb_generated_rv64_boot_info_dtb;

architecture sim of tb_generated_rv64_boot_info_dtb is
    constant CLK_PERIOD : time := 10 ns;
    constant MEM_WORDS  : integer := 2621440;
    constant PROGRESS_REPORT_INTERVAL : integer := 100000;

    constant MAGIC_ADDR_BITS        : std_logic_vector(63 downto 0) := x"0000000080600000";
    constant DONE_ADDR_BITS         : std_logic_vector(63 downto 0) := x"0000000080600008";
    constant HART_ID_ADDR_BITS      : std_logic_vector(63 downto 0) := x"0000000080600010";
    constant DTB_ADDR_ADDR_BITS     : std_logic_vector(63 downto 0) := x"0000000080600018";
    constant DTB_VALID_ADDR_BITS    : std_logic_vector(63 downto 0) := x"0000000080600020";
    constant RAM_BASE_ADDR_BITS     : std_logic_vector(63 downto 0) := x"0000000080600028";
    constant RAM_SIZE_ADDR_BITS     : std_logic_vector(63 downto 0) := x"0000000080600030";
    constant SERIAL_BASE_ADDR_BITS  : std_logic_vector(63 downto 0) := x"0000000080600038";
    constant SERIAL_MMIO_ADDR_BITS  : std_logic_vector(63 downto 0) := x"0000000080600040";
    constant MAP_LEN_ADDR_BITS      : std_logic_vector(63 downto 0) := x"0000000080600048";
    constant REGION0_BASE_ADDR_BITS : std_logic_vector(63 downto 0) := x"0000000080600050";
    constant REGION0_SIZE_ADDR_BITS : std_logic_vector(63 downto 0) := x"0000000080600058";
    constant REGION0_KIND_ADDR_BITS : std_logic_vector(63 downto 0) := x"0000000080600060";
    constant REGION1_BASE_ADDR_BITS : std_logic_vector(63 downto 0) := x"0000000080600068";
    constant REGION1_SIZE_ADDR_BITS : std_logic_vector(63 downto 0) := x"0000000080600070";
    constant REGION1_KIND_ADDR_BITS : std_logic_vector(63 downto 0) := x"0000000080600078";
    constant REGION2_BASE_ADDR_BITS : std_logic_vector(63 downto 0) := x"0000000080600080";
    constant REGION2_SIZE_ADDR_BITS : std_logic_vector(63 downto 0) := x"0000000080600088";
    constant REGION2_KIND_ADDR_BITS : std_logic_vector(63 downto 0) := x"0000000080600090";

    constant UART_ADDR            : std_logic_vector(63 downto 0) := x"0000000010000000";
    constant UART_MARKER_WORD     : std_logic_vector(31 downto 0) := x"42490D0A";
    constant PROOF_MAGIC_EXPECTED : std_logic_vector(63 downto 0) := x"42494F50524F4F46";
    constant PROOF_DONE_EXPECTED  : std_logic_vector(63 downto 0) := x"0000000000000001";
    constant BOOT_HART_ID         : std_logic_vector(63 downto 0) := x"0000000000000000";
    constant BOOT_DTB_ADDR        : std_logic_vector(63 downto 0) := x"0000000088000000";
    constant DTB_VALID_TRUE       : std_logic_vector(63 downto 0) := x"0000000000000001";
    constant RAM_BASE_EXPECTED    : std_logic_vector(63 downto 0) := x"0000000080000000";
    constant RAM_SIZE_EXPECTED    : std_logic_vector(63 downto 0) := x"0000000008000000";
    constant SERIAL_BASE_EXPECTED : std_logic_vector(63 downto 0) := x"0000000010000000";
    constant SERIAL_MMIO_TRUE     : std_logic_vector(63 downto 0) := x"0000000000000001";
    constant MAP_LEN_EXPECTED     : std_logic_vector(63 downto 0) := x"0000000000000003";
    constant REGION0_BASE_EXPECTED : std_logic_vector(63 downto 0) := x"0000000080000000";
    constant REGION0_SIZE_EXPECTED : std_logic_vector(63 downto 0) := x"0000000000200000";
    constant REGION0_KIND_EXPECTED : std_logic_vector(63 downto 0) := x"0000000000000002";
    constant REGION1_BASE_EXPECTED : std_logic_vector(63 downto 0) := x"0000000080200000";
    constant REGION1_SIZE_EXPECTED : std_logic_vector(63 downto 0) := x"0000000000200000";
    constant REGION1_KIND_EXPECTED : std_logic_vector(63 downto 0) := x"0000000000000008";
    constant REGION2_BASE_EXPECTED : std_logic_vector(63 downto 0) := x"0000000080400000";
    constant REGION2_SIZE_EXPECTED : std_logic_vector(63 downto 0) := x"0000000007C00000";
    constant REGION2_KIND_EXPECTED : std_logic_vector(63 downto 0) := x"0000000000000001";

    type byte_array_t is array (natural range <>) of std_logic_vector(7 downto 0);

    constant DTB_SIZE_BYTES      : integer := 239;
    constant DTB_BYTES           : byte_array_t(0 to DTB_SIZE_BYTES - 1) := (
        x"D0", x"0D", x"FE", x"ED", x"00", x"00", x"00", x"EF",
        x"00", x"00", x"00", x"38", x"00", x"00", x"00", x"D0",
        x"00", x"00", x"00", x"28", x"00", x"00", x"00", x"11",
        x"00", x"00", x"00", x"10", x"00", x"00", x"00", x"00",
        x"00", x"00", x"00", x"1F", x"00", x"00", x"00", x"98",
        x"00", x"00", x"00", x"00", x"00", x"00", x"00", x"00",
        x"00", x"00", x"00", x"00", x"00", x"00", x"00", x"00",
        x"00", x"00", x"00", x"01", x"00", x"00", x"00", x"00",
        x"00", x"00", x"00", x"03", x"00", x"00", x"00", x"04",
        x"00", x"00", x"00", x"00", x"00", x"00", x"00", x"02",
        x"00", x"00", x"00", x"03", x"00", x"00", x"00", x"04",
        x"00", x"00", x"00", x"0F", x"00", x"00", x"00", x"02",
        x"00", x"00", x"00", x"01", x"6D", x"65", x"6D", x"6F",
        x"72", x"79", x"40", x"38", x"30", x"30", x"30", x"30",
        x"30", x"30", x"30", x"00", x"00", x"00", x"00", x"03",
        x"00", x"00", x"00", x"10", x"00", x"00", x"00", x"1B",
        x"00", x"00", x"00", x"00", x"80", x"00", x"00", x"00",
        x"00", x"00", x"00", x"00", x"08", x"00", x"00", x"00",
        x"00", x"00", x"00", x"02", x"00", x"00", x"00", x"01",
        x"73", x"65", x"72", x"69", x"61", x"6C", x"40", x"31",
        x"30", x"30", x"30", x"30", x"30", x"30", x"30", x"00",
        x"00", x"00", x"00", x"03", x"00", x"00", x"00", x"10",
        x"00", x"00", x"00", x"1B", x"00", x"00", x"00", x"00",
        x"10", x"00", x"00", x"00", x"00", x"00", x"00", x"00",
        x"00", x"00", x"01", x"00", x"00", x"00", x"00", x"02",
        x"00", x"00", x"00", x"02", x"00", x"00", x"00", x"09",
        x"23", x"61", x"64", x"64", x"72", x"65", x"73", x"73",
        x"2D", x"63", x"65", x"6C", x"6C", x"73", x"00", x"23",
        x"73", x"69", x"7A", x"65", x"2D", x"63", x"65", x"6C",
        x"6C", x"73", x"00", x"72", x"65", x"67", x"00"
    );

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

    function hex_to_slv4(ch : character) return std_logic_vector is
    begin
        case ch is
            when '0' => return "0000";
            when '1' => return "0001";
            when '2' => return "0010";
            when '3' => return "0011";
            when '4' => return "0100";
            when '5' => return "0101";
            when '6' => return "0110";
            when '7' => return "0111";
            when '8' => return "1000";
            when '9' => return "1001";
            when 'A' | 'a' => return "1010";
            when 'B' | 'b' => return "1011";
            when 'C' | 'c' => return "1100";
            when 'D' | 'd' => return "1101";
            when 'E' | 'e' => return "1110";
            when others => return "1111";
        end case;
    end function;

    function hex_to_byte(text_value : string) return std_logic_vector is
        variable result : std_logic_vector(7 downto 0);
    begin
        result(7 downto 4) := hex_to_slv4(text_value(text_value'low));
        result(3 downto 0) := hex_to_slv4(text_value(text_value'low + 1));
        return result;
    end function;

    function hex_to_word64(text_value : string) return std_logic_vector is
        variable result : std_logic_vector(63 downto 0);
        variable high_bit : integer;
    begin
        for i in 0 to 15 loop
            high_bit := 63 - (i * 4);
            result(high_bit downto high_bit - 3) := hex_to_slv4(text_value(text_value'low + i));
        end loop;
        return result;
    end function;

    procedure load_preload_file(
        label_name : in string;
        path : in string;
        base_offset : in integer;
        variable mem_state : inout mem_t
    ) is
        file input_file : text open read_mode is path;
        variable word_idx : integer;
        variable byte_idx : integer;
        variable bytes_loaded : integer := 0;
        variable words_loaded : integer := 0;
        variable row_len : integer;
        variable current_word : std_logic_vector(63 downto 0);
        variable next_word : std_logic_vector(63 downto 0);
        variable row : line;
    begin
        while not endfile(input_file) loop
            readline(input_file, row);
            row_len := row.all'length;
            if row_len = 16 then
                assert (base_offset mod 8) = 0
                    report "word preload requires 8-byte aligned base offset for " & label_name
                    severity failure;
                word_idx := (base_offset / 8) + words_loaded;
                if word_idx < MEM_WORDS then
                    next_word := hex_to_word64(row.all(1 to 16));
                    mem_state(word_idx) := next_word;
                end if;
                words_loaded := words_loaded + 1;
                bytes_loaded := bytes_loaded + 8;
                if (words_loaded mod PROGRESS_REPORT_INTERVAL) = 0 then
                    report "PRELOAD_" & label_name & "_WORDS: " & integer'image(words_loaded);
                    report "PRELOAD_" & label_name & "_BYTES: " & integer'image(bytes_loaded);
                end if;
            elsif row_len = 2 then
                word_idx := (base_offset + bytes_loaded) / 8;
                byte_idx := (base_offset + bytes_loaded) mod 8;
                if word_idx < MEM_WORDS then
                    current_word := mem_state(word_idx);
                    current_word((byte_idx * 8) + 7 downto byte_idx * 8) := hex_to_byte(row.all(1 to 2));
                    mem_state(word_idx) := current_word;
                end if;
                bytes_loaded := bytes_loaded + 1;
                if (bytes_loaded mod PROGRESS_REPORT_INTERVAL) = 0 then
                    report "PRELOAD_" & label_name & "_BYTES: " & integer'image(bytes_loaded);
                end if;
            elsif row_len /= 0 then
                assert false
                    report "unsupported preload line width for " & label_name & ": " & integer'image(row_len)
                    severity failure;
            end if;
            deallocate(row);
        end loop;
        if words_loaded > 0 then
            report "PRELOAD_" & label_name & "_DONE_WORDS: " & integer'image(words_loaded);
        end if;
        report "PRELOAD_" & label_name & "_DONE_BYTES: " & integer'image(bytes_loaded);
    end procedure;

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

    function hex8(bits : std_logic_vector(7 downto 0)) return string is
        variable result : string(1 to 2);
    begin
        result(1) := hex_char(bits(7 downto 4));
        result(2) := hex_char(bits(3 downto 0));
        return result;
    end function;

    function mem_index(addr : std_logic_vector(63 downto 0)) return integer is
    begin
        return safe_index(addr(24 downto 3));
    end function;

    function dtb_offset(addr : std_logic_vector(63 downto 0)) return integer is
        variable addr_int : integer;
        variable base_int : integer;
    begin
        addr_int := safe_index(addr(30 downto 0));
        base_int := safe_index(BOOT_DTB_ADDR(30 downto 0));
        return addr_int - base_int;
    end function;

    function dtb_in_range(addr : std_logic_vector(63 downto 0)) return boolean is
        variable offs : integer;
    begin
        offs := dtb_offset(addr);
        return offs >= 0 and offs < DTB_SIZE_BYTES;
    end function;

    function dtb_word(addr : std_logic_vector(63 downto 0)) return std_logic_vector is
        variable result : std_logic_vector(63 downto 0) := (others => '0');
        variable base_offs : integer;
    begin
        base_offs := (dtb_offset(addr) / 8) * 8;
        for i in 0 to 7 loop
            if base_offs + i >= 0 and base_offs + i < DTB_SIZE_BYTES then
                result((i * 8) + 7 downto i * 8) := DTB_BYTES(base_offs + i);
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

    signal mem : mem_t := (others => (others => '0'));
    signal uart_word : std_logic_vector(31 downto 0) := (others => '0');
    signal uart_marker_seen : boolean := false;
    signal dtb_probe_seen : boolean := false;
    signal dtb_probe_addr : std_logic_vector(63 downto 0) := (others => '0');
    signal dmem_write_seen : boolean := false;
    signal dmem_write_addr : std_logic_vector(63 downto 0) := (others => '0');
    signal done : boolean := false;
begin
    preload_mem : process
        variable preload : mem_t := (others => (others => '0'));
    begin
        report "PRELOAD_PROCESS_START";
        report "PRELOAD_FW_START";
        load_preload_file("FW", FW_HEX_PATH, 0, preload);
        report "PRELOAD_PAYLOAD_START";
        load_preload_file("PAYLOAD", PAYLOAD_HEX_PATH, 16#200000#, preload);
        report "PRELOAD_MEM_ASSIGN";
        mem <= preload;
        report "PRELOAD_PROCESS_DONE";
        wait;
    end process;

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
        variable next_uart_word : std_logic_vector(31 downto 0);
    begin
        if rising_edge(clk) then
            if dmem_re = '1' and dtb_in_range(dmem_addr) then
                dtb_probe_seen <= true;
                if not dtb_probe_seen then
                    dtb_probe_addr <= dmem_addr;
                end if;
            end if;
            if dmem_re = '1' and now <= 1000 ns then
                report "DMEM_READ_EVENT_ADDR_HEX32: " & hex32(dmem_addr(31 downto 0));
                report "DMEM_READ_EVENT_DATA_HEX32: " & hex32(dmem_rdata(31 downto 0));
            end if;

            if dmem_we = '1' and dmem_addr = UART_ADDR and dmem_wstrb(0) = '1' then
                if now <= 1000 ns then
                    report "DMEM_WRITE_EVENT_ADDR_HEX32: " & hex32(dmem_addr(31 downto 0));
                    report "DMEM_WRITE_EVENT_DATA_HEX32: " & hex32(dmem_wdata(31 downto 0));
                end if;
                report "UART_CHAR_HEX8: " & hex8(dmem_wdata(7 downto 0));
                next_uart_word := uart_word(23 downto 0) & dmem_wdata(7 downto 0);
                uart_word <= next_uart_word;
                if next_uart_word = UART_MARKER_WORD then
                    uart_marker_seen <= true;
                end if;
            elsif dmem_we = '1' then
                if now <= 1000 ns then
                    report "DMEM_WRITE_EVENT_ADDR_HEX32: " & hex32(dmem_addr(31 downto 0));
                    report "DMEM_WRITE_EVENT_DATA_HEX32: " & hex32(dmem_wdata(31 downto 0));
                end if;
                dmem_write_seen <= true;
                dmem_write_addr <= dmem_addr;
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

    dmem_rdata <= dtb_word(dmem_addr) when dtb_in_range(dmem_addr) else
        mem(mem_index(dmem_addr))
        when mem_index(dmem_addr) < MEM_WORDS
        else (others => '0');

    process
        variable cycles : integer := 0;
    begin
        reset_n <= '0';
        wait for CLK_PERIOD * 5;
        reset_n <= '1';

        while halt = '0' and trap = '0' and cycles < MAX_CYCLES loop
            wait for CLK_PERIOD;
            cycles := cycles + 1;
            if cycles <= 80 then
                report "HEARTBEAT_CYCLES: " & integer'image(cycles);
                report "HEARTBEAT_PC_HEX32: " & hex32(debug_pc(31 downto 0));
                report "HEARTBEAT_PRIV_MODE: " & integer'image(safe_index(debug_priv_mode));
                report "HEARTBEAT_LAST_LOAD_HEX32: " & hex32(debug_last_load_value(31 downto 0));
            elsif (cycles mod PROGRESS_REPORT_INTERVAL) = 0 then
                report "PROGRESS_CYCLES: " & integer'image(cycles);
                report "PROGRESS_PC_HEX32: " & hex32(debug_pc(31 downto 0));
                report "PROGRESS_PRIV_MODE: " & integer'image(safe_index(debug_priv_mode));
                report "PROGRESS_LAST_LOAD_HEX32: " & hex32(debug_last_load_value(31 downto 0));
                report "PROGRESS_UART_WORD_HEX32: " & hex32(uart_word);
            end if;
        end loop;

        report "CYCLES: " & integer'image(cycles);
        report "MAGIC_LOW32: " & integer'image(word32_to_report_int(mem(mem_index(MAGIC_ADDR_BITS))(31 downto 0)));
        report "DONE_LOW32: " & integer'image(word32_to_report_int(mem(mem_index(DONE_ADDR_BITS))(31 downto 0)));
        report "HART_ID_LOW32: " & integer'image(word32_to_report_int(mem(mem_index(HART_ID_ADDR_BITS))(31 downto 0)));
        report "DTB_ADDR_LOW32: " & integer'image(word32_to_report_int(mem(mem_index(DTB_ADDR_ADDR_BITS))(31 downto 0)));
        report "DTB_ADDR_HEX32: " & hex32(mem(mem_index(DTB_ADDR_ADDR_BITS))(31 downto 0));
        report "DTB_VALID_LOW32: " & integer'image(word32_to_report_int(mem(mem_index(DTB_VALID_ADDR_BITS))(31 downto 0)));
        report "RAM_BASE_LOW32: " & integer'image(word32_to_report_int(mem(mem_index(RAM_BASE_ADDR_BITS))(31 downto 0)));
        report "RAM_SIZE_LOW32: " & integer'image(word32_to_report_int(mem(mem_index(RAM_SIZE_ADDR_BITS))(31 downto 0)));
        report "SERIAL_BASE_LOW32: " & integer'image(word32_to_report_int(mem(mem_index(SERIAL_BASE_ADDR_BITS))(31 downto 0)));
        report "SERIAL_MMIO_LOW32: " & integer'image(word32_to_report_int(mem(mem_index(SERIAL_MMIO_ADDR_BITS))(31 downto 0)));
        report "MAP_LEN_LOW32: " & integer'image(word32_to_report_int(mem(mem_index(MAP_LEN_ADDR_BITS))(31 downto 0)));
        report "REGION0_BASE_LOW32: " & integer'image(word32_to_report_int(mem(mem_index(REGION0_BASE_ADDR_BITS))(31 downto 0)));
        report "REGION0_BASE_HEX32: " & hex32(mem(mem_index(REGION0_BASE_ADDR_BITS))(31 downto 0));
        report "REGION0_SIZE_LOW32: " & integer'image(word32_to_report_int(mem(mem_index(REGION0_SIZE_ADDR_BITS))(31 downto 0)));
        report "REGION0_SIZE_HEX32: " & hex32(mem(mem_index(REGION0_SIZE_ADDR_BITS))(31 downto 0));
        report "REGION0_KIND_LOW32: " & integer'image(word32_to_report_int(mem(mem_index(REGION0_KIND_ADDR_BITS))(31 downto 0)));
        report "REGION1_BASE_LOW32: " & integer'image(word32_to_report_int(mem(mem_index(REGION1_BASE_ADDR_BITS))(31 downto 0)));
        report "REGION1_BASE_HEX32: " & hex32(mem(mem_index(REGION1_BASE_ADDR_BITS))(31 downto 0));
        report "REGION1_SIZE_LOW32: " & integer'image(word32_to_report_int(mem(mem_index(REGION1_SIZE_ADDR_BITS))(31 downto 0)));
        report "REGION1_SIZE_HEX32: " & hex32(mem(mem_index(REGION1_SIZE_ADDR_BITS))(31 downto 0));
        report "REGION1_KIND_LOW32: " & integer'image(word32_to_report_int(mem(mem_index(REGION1_KIND_ADDR_BITS))(31 downto 0)));
        report "REGION2_BASE_LOW32: " & integer'image(word32_to_report_int(mem(mem_index(REGION2_BASE_ADDR_BITS))(31 downto 0)));
        report "REGION2_BASE_HEX32: " & hex32(mem(mem_index(REGION2_BASE_ADDR_BITS))(31 downto 0));
        report "REGION2_SIZE_LOW32: " & integer'image(word32_to_report_int(mem(mem_index(REGION2_SIZE_ADDR_BITS))(31 downto 0)));
        report "REGION2_SIZE_HEX32: " & hex32(mem(mem_index(REGION2_SIZE_ADDR_BITS))(31 downto 0));
        report "REGION2_KIND_LOW32: " & integer'image(word32_to_report_int(mem(mem_index(REGION2_KIND_ADDR_BITS))(31 downto 0)));
        report "RAM_BASE_HEX32: " & hex32(mem(mem_index(RAM_BASE_ADDR_BITS))(31 downto 0));
        report "RAM_SIZE_HEX32: " & hex32(mem(mem_index(RAM_SIZE_ADDR_BITS))(31 downto 0));
        report "SERIAL_BASE_HEX32: " & hex32(mem(mem_index(SERIAL_BASE_ADDR_BITS))(31 downto 0));
        report "DTB_PROBE_SEEN: " & boolean'image(dtb_probe_seen);
        report "DTB_PROBE_ADDR_HEX32: " & hex32(dtb_probe_addr(31 downto 0));
        report "UART_BYTES_LOW32: " & integer'image(word32_to_report_int(uart_word));
        report "UART_MARKER_SEEN: " & boolean'image(uart_marker_seen);
        report "PRIV_MODE: " & integer'image(safe_index(debug_priv_mode));
        report "HALT_SEEN: " & std_logic'image(halt);
        report "TRAP_SEEN: " & std_logic'image(trap);
        report "PC_LOW32: " & integer'image(word32_to_report_int(debug_pc(31 downto 0)));
        report "PC_HEX32: " & hex32(debug_pc(31 downto 0));
        report "DMEM_WRITE_SEEN: " & boolean'image(dmem_write_seen);
        report "DMEM_WRITE_ADDR_HEX32: " & hex32(dmem_write_addr(31 downto 0));
        if (halt = '1' or trap = '1') and
            mem(mem_index(MAGIC_ADDR_BITS)) = PROOF_MAGIC_EXPECTED and
            mem(mem_index(DONE_ADDR_BITS)) = PROOF_DONE_EXPECTED and
            mem(mem_index(HART_ID_ADDR_BITS)) = BOOT_HART_ID and
            mem(mem_index(DTB_ADDR_ADDR_BITS)) = BOOT_DTB_ADDR and
            mem(mem_index(DTB_VALID_ADDR_BITS)) = DTB_VALID_TRUE and
            mem(mem_index(RAM_BASE_ADDR_BITS)) = RAM_BASE_EXPECTED and
            mem(mem_index(RAM_SIZE_ADDR_BITS)) = RAM_SIZE_EXPECTED and
            mem(mem_index(SERIAL_BASE_ADDR_BITS)) = SERIAL_BASE_EXPECTED and
            mem(mem_index(SERIAL_MMIO_ADDR_BITS)) = SERIAL_MMIO_TRUE and
            mem(mem_index(MAP_LEN_ADDR_BITS)) = MAP_LEN_EXPECTED and
            mem(mem_index(REGION0_BASE_ADDR_BITS)) = REGION0_BASE_EXPECTED and
            mem(mem_index(REGION0_SIZE_ADDR_BITS)) = REGION0_SIZE_EXPECTED and
            mem(mem_index(REGION0_KIND_ADDR_BITS)) = REGION0_KIND_EXPECTED and
            mem(mem_index(REGION1_BASE_ADDR_BITS)) = REGION1_BASE_EXPECTED and
            mem(mem_index(REGION1_SIZE_ADDR_BITS)) = REGION1_SIZE_EXPECTED and
            mem(mem_index(REGION1_KIND_ADDR_BITS)) = REGION1_KIND_EXPECTED and
            mem(mem_index(REGION2_BASE_ADDR_BITS)) = REGION2_BASE_EXPECTED and
            mem(mem_index(REGION2_SIZE_ADDR_BITS)) = REGION2_SIZE_EXPECTED and
            mem(mem_index(REGION2_KIND_ADDR_BITS)) = REGION2_KIND_EXPECTED and
            uart_marker_seen and
            debug_priv_mode = "01" and
            dtb_probe_seen and
            dtb_probe_addr = BOOT_DTB_ADDR then
            report "GENERATED_RV64_BOOT_INFO_DTB: PASS";
        else
            report "GENERATED_RV64_BOOT_INFO_DTB: FAIL";
        end if;
        done <= true;
        wait;
    end process;
end architecture sim;
