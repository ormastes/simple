library ieee;
use ieee.std_logic_1164.all;

entity tb_addition_uart_demo is
end entity tb_addition_uart_demo;

architecture sim of tb_addition_uart_demo is
    constant CLK_PERIOD : time := 20 ns;
    signal clk25   : std_logic := '0';
    signal rst_n   : std_logic := '0';
    signal uart_tx : std_logic;
    signal led     : std_logic_vector(0 downto 0);
begin
    clk25 <= not clk25 after CLK_PERIOD / 2;

    dut : entity work.mlk_s02_100t_addition_uart_demo_top
        port map (
            clk25   => clk25,
            rst_n   => rst_n,
            uart_tx => uart_tx,
            uart_rx => '1',
            led     => led
        );

    process
    begin
        wait for 100 ns;
        rst_n <= '1';
        wait for 1 ms;
        assert led(0) = '1' report "3 + 5 should drive LED0 high" severity failure;
        assert uart_tx = '0' or uart_tx = '1' report "uart_tx should be driven" severity failure;
        report "addition_uart_demo PASS";
        wait;
    end process;
end architecture sim;

