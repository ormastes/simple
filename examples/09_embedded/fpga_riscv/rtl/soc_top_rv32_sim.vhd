library ieee;
use ieee.std_logic_1164.all;

entity soc_top_rv32_sim is
  port (
    clk : in std_logic;
    rst : in std_logic;
    uart_tx : out std_logic;
    uart_rx : in std_logic
  );
end entity soc_top_rv32_sim;

architecture rtl of soc_top_rv32_sim is
begin
  u_core : entity work.rv32_exec_core
    port map (clk => clk, rst => rst, uart_tx => uart_tx);
end architecture rtl;
