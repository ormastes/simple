library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
library unisim;
use unisim.vcomponents.all;

entity soc_top_rv32 is
  port (
    uart_tx : out std_logic
  );
end entity soc_top_rv32;

architecture rtl of soc_top_rv32 is
  signal cfgclk  : std_logic;
  signal cfgmclk : std_logic;
  signal di      : std_logic_vector(3 downto 0);
  signal eos     : std_logic;
  signal preq    : std_logic;
  signal rst_q   : std_logic := '1';
  signal rst_cnt : unsigned(7 downto 0) := (others => '0');
begin
  u_startup : STARTUPE3
    generic map (PROG_USR => "FALSE", SIM_CCLK_FREQ => 0.0)
    port map (
      CFGCLK => cfgclk, CFGMCLK => cfgmclk, DI => di, EOS => eos, PREQ => preq,
      DO => "0000", DTS => "1111", FCSBO => '1', FCSBTS => '1', GSR => '0', GTS => '0',
      KEYCLEARB => '1', PACK => '0', USRCCLKO => '0', USRCCLKTS => '1',
      USRDONEO => '1', USRDONETS => '1'
    );

  process(cfgmclk)
  begin
    if rising_edge(cfgmclk) then
      if rst_cnt /= x"ff" then
        rst_cnt <= rst_cnt + 1;
        rst_q <= '1';
      else
        rst_q <= '0';
      end if;
    end if;
  end process;

  u_core : entity work.rv32_exec_core
    port map (clk => cfgmclk, rst => rst_q, uart_tx => uart_tx);
end architecture rtl;
