library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

entity mlk_s02_100t_addition_uart_dualpin_demo_top is
    port (
        clk25    : in  std_logic;
        uart_tx0 : out std_logic;
        uart_tx1 : out std_logic;
        led      : out std_logic_vector(0 downto 0)
    );
end entity mlk_s02_100t_addition_uart_dualpin_demo_top;

architecture rtl of mlk_s02_100t_addition_uart_dualpin_demo_top is
    constant CLK_HZ  : integer := 50000000;
    constant BAUD    : integer := 115200;
    constant DIVISOR : integer := CLK_HZ / BAUD;

    type msg_t is array (natural range <>) of std_logic_vector(7 downto 0);
    constant MSG : msg_t := (
        x"41", x"44", x"44", x"20", x"33", x"2b", x"35", x"3d", x"38", x"0a"
    );

    signal sum      : std_logic_vector(4 downto 0);
    signal tx_shift : std_logic_vector(9 downto 0) := (others => '1');
    signal tx_busy  : std_logic := '0';
    signal tx_line  : std_logic := '1';
    signal baud_cnt : integer range 0 to DIVISOR - 1 := 0;
    signal bit_idx  : integer range 0 to 9 := 0;
    signal msg_idx  : integer range 0 to MSG'length - 1 := 0;
    signal gap_cnt  : integer range 0 to CLK_HZ / 2 := 0;
begin
    u_add : entity work.addition_demo
        port map (
            a   => "0011",
            b   => "0101",
            sum => sum
        );

    led(0) <= sum(3);
    uart_tx0 <= tx_line;
    uart_tx1 <= tx_line;

    process(clk25)
    begin
        if rising_edge(clk25) then
            if tx_busy = '1' then
                if baud_cnt = DIVISOR - 1 then
                    baud_cnt <= 0;
                    tx_line <= tx_shift(0);
                    tx_shift <= '1' & tx_shift(9 downto 1);
                    if bit_idx = 9 then
                        bit_idx <= 0;
                        tx_busy <= '0';
                        if msg_idx = MSG'length - 1 then
                            msg_idx <= 0;
                            gap_cnt <= CLK_HZ / 2;
                        else
                            msg_idx <= msg_idx + 1;
                        end if;
                    else
                        bit_idx <= bit_idx + 1;
                    end if;
                else
                    baud_cnt <= baud_cnt + 1;
                end if;
            elsif gap_cnt /= 0 then
                gap_cnt <= gap_cnt - 1;
                tx_line <= '1';
            else
                tx_shift <= '1' & MSG(msg_idx) & '0';
                tx_busy <= '1';
                baud_cnt <= 0;
                bit_idx <= 0;
            end if;
        end if;
    end process;
end architecture rtl;

