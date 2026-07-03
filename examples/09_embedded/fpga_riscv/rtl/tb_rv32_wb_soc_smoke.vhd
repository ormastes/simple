library ieee;
use ieee.std_logic_1164.all;

entity tb_rv32_wb_soc_smoke is
end entity tb_rv32_wb_soc_smoke;

architecture sim of tb_rv32_wb_soc_smoke is
  signal clk : std_logic := '0';
  signal rst : std_logic := '1';
  signal uart_tx : std_logic;
  signal tx_seen : std_logic := '0';
  signal last_tx : std_logic := '1';
begin
  clk <= not clk after 5 ns;

  dut : entity work.soc_top_rv32_sim
    port map (
      clk => clk,
      rst => rst,
      uart_tx => uart_tx,
      uart_rx => '1'
    );

  process
  begin
    wait for 200 ns;
    rst <= '0';
    wait for 20 ms;
    assert tx_seen = '1' report "RV32_UART_TX_ACTIVITY_MISSING" severity failure;
    report "RV32_UART_TX_ACTIVITY_SEEN" severity note;
    wait;
  end process;

  process(clk)
  begin
    if rising_edge(clk) then
      if last_tx = '1' and uart_tx = '0' then
        tx_seen <= '1';
      end if;
      last_tx <= uart_tx;
    end if;
  end process;
end architecture sim;
