-- ZedBoard Top-Level Wrapper for RV32I CPU
-- 100 MHz clock, 8 LEDs output, 8 switches input, 5 buttons
-- 4KB instruction RAM + 4KB data RAM (block RAM)

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

entity zedboard_top is
    port (
        GCLK      : in  std_logic;  -- 100 MHz system clock (Y9)
        BTNC      : in  std_logic;  -- Center button = reset
        -- User I/O
        SW        : in  std_logic_vector(7 downto 0);   -- 8 switches
        BTNU      : in  std_logic;
        BTND      : in  std_logic;
        BTNL      : in  std_logic;
        BTNR      : in  std_logic;
        LD        : out std_logic_vector(7 downto 0)    -- 8 LEDs
    );
end entity zedboard_top;

architecture rtl of zedboard_top is
    -- Clock and reset
    signal clk     : std_logic;
    signal reset_n : std_logic;

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

    -- Memory (4KB each = 1024 words)
    type mem_t is array (0 to 1023) of std_logic_vector(31 downto 0);

    -- Simple test program: count on LEDs
    -- Address 0x80000000 = LED output register (memory-mapped I/O)
    -- Address 0x80000004 = Switch input register
    signal imem : mem_t := (
        -- Program: Read switches, add 1 each loop, write to LEDs
        --  0: addi x1, x0, 0          # counter = 0
        0  => x"00000093",
        --  4: lui  x2, 0x80000        # x2 = 0x80000000 (I/O base)
        1  => x"80000137",
        --  8: lw   x3, 4(x2)          # x3 = switches
        2  => x"00412183",
        -- 12: add  x1, x1, x3         # counter += switches
        3  => x"003080B3",
        -- 16: sw   x1, 0(x2)          # LEDs = counter
        4  => x"00112023",
        -- 20: addi x4, x0, 1          # delay constant
        5  => x"00100213",
        -- 24: lui  x5, 0x00010        # delay count = 0x10000
        6  => x"000102B7",
        -- 28: sub  x5, x5, x4         # delay--
        7  => x"404282B3",
        -- 32: bne  x5, x0, -4         # loop while delay > 0
        8  => x"FE029EE3",
        -- 36: jal  x0, -28            # jump back to load switches
        9  => x"FE5FF06F",
        others => x"00000013"  -- NOP (addi x0, x0, 0)
    );

    signal dmem : mem_t := (others => (others => '0'));

    -- I/O registers
    signal led_reg : std_logic_vector(7 downto 0) := (others => '0');

begin
    clk     <= GCLK;
    reset_n <= not BTNC;

    -- CPU core
    u_cpu : entity work.rv32i_core
        generic map (RESET_ADDR => x"00000000")
        port map (
            clk        => clk,
            reset_n    => reset_n,
            imem_addr  => imem_addr,
            imem_data  => imem_data,
            dmem_addr  => dmem_addr,
            dmem_wdata => dmem_wdata,
            dmem_rdata => dmem_rdata,
            dmem_we    => dmem_we,
            dmem_re    => dmem_re,
            dmem_width => dmem_width,
            halted     => halted
        );

    -- Instruction memory (read-only, combinational)
    imem_data <= imem(to_integer(unsigned(imem_addr(11 downto 2))))
                 when unsigned(imem_addr(31 downto 12)) = 0
                 else x"00000013";  -- NOP for out-of-range

    -- Data memory + memory-mapped I/O
    process(clk)
        variable addr_word : integer;
    begin
        if rising_edge(clk) then
            -- Memory-mapped I/O: 0x80000000
            if dmem_we = '1' then
                if dmem_addr(31) = '1' then
                    -- I/O write: LED register
                    if dmem_addr(3 downto 0) = x"0" then
                        led_reg <= dmem_wdata(7 downto 0);
                    end if;
                else
                    -- RAM write
                    addr_word := to_integer(unsigned(dmem_addr(11 downto 2)));
                    dmem(addr_word) <= dmem_wdata;
                end if;
            end if;
        end if;
    end process;

    -- Data memory read (combinational)
    process(dmem_addr, dmem_re, dmem, led_reg, SW, BTNU, BTND, BTNL, BTNR)
        variable addr_word : integer;
    begin
        dmem_rdata <= (others => '0');
        if dmem_re = '1' then
            if dmem_addr(31) = '1' then
                -- I/O read
                case dmem_addr(3 downto 0) is
                    when x"0" => dmem_rdata(7 downto 0) <= led_reg;
                    when x"4" => dmem_rdata(7 downto 0) <= SW;
                    when x"8" => dmem_rdata(3 downto 0) <= BTNU & BTND & BTNL & BTNR;
                    when others => dmem_rdata <= (others => '0');
                end case;
            else
                addr_word := to_integer(unsigned(dmem_addr(11 downto 2)));
                dmem_rdata <= dmem(addr_word);
            end if;
        end if;
    end process;

    -- LED output
    LD <= led_reg;

end architecture rtl;
