library ieee;
use ieee.std_logic_1164.all;

entity mlk_s02_100t_addition_demo_top is
    port (
        clk25   : in  std_logic;
        rst_n   : in  std_logic;
        uart_tx : out std_logic;
        uart_rx : in  std_logic;
        led     : out std_logic_vector(7 downto 0);
        btn     : in  std_logic_vector(3 downto 0)
    );
end entity mlk_s02_100t_addition_demo_top;

architecture rtl of mlk_s02_100t_addition_demo_top is
    signal sum : std_logic_vector(4 downto 0);
begin
    -- Board smoke behavior: add the 4 button bits to constant 5 and show the
    -- 5-bit result on LEDs. With no buttons pressed, LED[4:0] shows 5.
    u_add : entity work.addition_demo
        port map (
            a   => btn,
            b   => "0101",
            sum => sum
        );

    led(4 downto 0) <= sum when rst_n = '1' else (others => '0');
    led(7 downto 5) <= (others => '0');
    uart_tx <= '1';
end architecture rtl;

