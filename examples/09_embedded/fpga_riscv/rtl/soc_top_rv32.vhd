library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

entity soc_top_rv32 is
  port (
    clk : in std_logic;
    uart_tx : out std_logic
  );
end entity soc_top_rv32;

architecture rtl of soc_top_rv32 is
  signal rst_q   : std_logic := '1';
  signal rst_cnt : unsigned(7 downto 0) := (others => '0');
begin
  process(clk)
  begin
    if rising_edge(clk) then
      if rst_cnt /= x"ff" then
        rst_cnt <= rst_cnt + 1;
        rst_q <= '1';
      else
        rst_q <= '0';
      end if;
    end if;
  end process;

  u_core : entity work.rv32_exec_core
    port map (clk => clk, rst => rst_q, uart_tx => uart_tx);
end architecture rtl;
