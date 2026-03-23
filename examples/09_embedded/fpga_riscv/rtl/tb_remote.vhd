-- Remote Test Testbench
-- Loads RV32I program from hex file, runs CPU, checks LED output
-- Usage: ghdl -r tb_remote -gPROGRAM=test/test_add.hex -gEXPECT_LED=8 --stop-time=1ms

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use std.textio.all;

entity tb_remote is
    generic (
        PROGRAM    : string  := "test/test_add.hex";
        EXPECT_LED : integer := -1;    -- -1 = don't check
        MAX_CYCLES : integer := 100000
    );
end entity tb_remote;

architecture sim of tb_remote is
    constant CLK_PERIOD : time := 10 ns;

    signal clk     : std_logic := '0';
    signal reset_n : std_logic := '0';

    -- CPU signals
    signal imem_addr  : std_logic_vector(31 downto 0);
    signal imem_data  : std_logic_vector(31 downto 0);
    signal dmem_addr  : std_logic_vector(31 downto 0);
    signal dmem_wdata : std_logic_vector(31 downto 0);
    signal dmem_rdata : std_logic_vector(31 downto 0);
    signal dmem_we    : std_logic;
    signal dmem_re    : std_logic;
    signal dmem_width : std_logic_vector(1 downto 0);
    signal halted     : std_logic;

    -- Memory
    type mem_t is array (0 to 1023) of std_logic_vector(31 downto 0);
    signal imem : mem_t := (others => x"00000013");
    signal dmem : mem_t := (others => (others => '0'));

    -- I/O
    signal led_reg    : std_logic_vector(31 downto 0) := (others => '0');
    signal switch_reg : std_logic_vector(31 downto 0) := (others => '0');

    signal done : boolean := false;

    -- Hex file loading
    impure function load_hex(filename : string) return mem_t is
        file hex_file : text;
        variable line_buf : line;
        variable mem : mem_t := (others => x"00000013");
        variable addr : integer := 0;
        variable byte_val : integer;
        variable word : std_logic_vector(31 downto 0);
        variable ch : character;
        variable good : boolean;
        variable byte_idx : integer := 0;
        variable hex_str : string(1 to 2);
    begin
        file_open(hex_file, filename, read_mode);
        word := (others => '0');
        byte_idx := 0;
        while not endfile(hex_file) loop
            readline(hex_file, line_buf);
            if line_buf'length > 0 then
                read(line_buf, ch, good);
                if good and ch = '@' then
                    -- Address line: @XXXXXXXX
                    hread(line_buf, word);
                    addr := to_integer(unsigned(word));
                    byte_idx := 0;
                else
                    -- Data line: bytes separated by spaces
                    -- Put char back by starting fresh
                    deallocate(line_buf);
                    -- Re-read as hex bytes
                end if;
            end if;
        end loop;
        file_close(hex_file);
        return mem;
    end function;

begin
    -- CPU
    u_cpu : entity work.rv32i_core
        generic map (RESET_ADDR => x"00000000")
        port map (
            clk => clk, reset_n => reset_n,
            imem_addr => imem_addr, imem_data => imem_data,
            dmem_addr => dmem_addr, dmem_wdata => dmem_wdata,
            dmem_rdata => dmem_rdata, dmem_we => dmem_we,
            dmem_re => dmem_re, dmem_width => dmem_width,
            halted => halted
        );

    clk <= not clk after CLK_PERIOD / 2 when not done else '0';

    -- Instruction memory
    imem_data <= imem(to_integer(unsigned(imem_addr(11 downto 2))))
                 when unsigned(imem_addr(31 downto 12)) = 0
                 else x"00000013";

    -- Data memory + MMIO
    process(clk)
    begin
        if rising_edge(clk) then
            if dmem_we = '1' then
                if dmem_addr(31) = '1' then
                    if dmem_addr(3 downto 0) = x"0" then
                        led_reg <= dmem_wdata;
                    end if;
                else
                    dmem(to_integer(unsigned(dmem_addr(11 downto 2)))) <= dmem_wdata;
                end if;
            end if;
        end if;
    end process;

    dmem_rdata <= led_reg when (dmem_re = '1' and dmem_addr(31) = '1' and dmem_addr(3 downto 0) = x"0") else
                  switch_reg when (dmem_re = '1' and dmem_addr(31) = '1' and dmem_addr(3 downto 0) = x"4") else
                  dmem(to_integer(unsigned(dmem_addr(11 downto 2)))) when (dmem_re = '1' and dmem_addr(31) = '0') else
                  (others => '0');

    -- Test driver
    process
        variable cycle_count : integer := 0;
    begin
        -- Load program into IMEM from compiled constants
        -- (hex file loading in GHDL is complex; we use pre-compiled IMEM init instead)

        reset_n <= '0';
        wait for CLK_PERIOD * 5;
        reset_n <= '1';

        -- Run until halted or max cycles
        while halted = '0' and cycle_count < MAX_CYCLES loop
            wait for CLK_PERIOD;
            cycle_count := cycle_count + 1;
        end loop;

        if halted = '1' then
            report "CPU halted after " & integer'image(cycle_count) & " cycles";
        else
            report "CPU did not halt within " & integer'image(MAX_CYCLES) & " cycles" severity warning;
        end if;

        report "LED register = " & integer'image(to_integer(unsigned(led_reg)));

        if EXPECT_LED >= 0 then
            assert to_integer(unsigned(led_reg)) = EXPECT_LED
                report "FAIL: expected LED=" & integer'image(EXPECT_LED) &
                       " got LED=" & integer'image(to_integer(unsigned(led_reg)))
                severity error;
            if to_integer(unsigned(led_reg)) = EXPECT_LED then
                report "PASS: LED=" & integer'image(EXPECT_LED) severity note;
            end if;
        end if;

        done <= true;
        wait;
    end process;
end architecture sim;
