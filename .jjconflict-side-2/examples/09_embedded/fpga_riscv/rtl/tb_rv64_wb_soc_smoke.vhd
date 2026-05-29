-- tb_rv64_wb_soc_smoke.vhd — Smoke testbench for RV64GC Wishbone SoC
--
-- Drives clk (100 MHz) and rst, monitors uart_tx for output.
-- Uses generic MAX_CYCLES timeout to prevent infinite simulation.
-- Matches the soc_top_rv64 entity interface from generate_soc_top_vhdl_rv64().
--
-- VHDL-2008

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

entity tb_rv64_wb_soc_smoke is
  generic (
    MAX_CYCLES : integer := 500000
  );
end entity tb_rv64_wb_soc_smoke;

architecture sim of tb_rv64_wb_soc_smoke is

  -- Clock period for 100 MHz
  constant CLK_PERIOD : time := 10 ns;

  -- DUT signals
  signal clk     : std_logic := '0';
  signal rst     : std_logic := '1';
  signal uart_tx : std_logic;
  signal uart_rx : std_logic := '1';  -- idle high

  -- Cycle counter
  signal cycle_count : integer := 0;

  -- UART capture
  signal uart_tx_prev : std_logic := '1';
  signal uart_activity : boolean := false;

begin

  -- ========================================================================
  -- Clock generation — 100 MHz (10 ns period)
  -- ========================================================================
  clk_proc : process
  begin
    clk <= '0';
    wait for CLK_PERIOD / 2;
    clk <= '1';
    wait for CLK_PERIOD / 2;
  end process clk_proc;

  -- ========================================================================
  -- DUT instantiation — soc_top_rv64
  -- ========================================================================
  dut : entity work.soc_top_rv64
    generic map (
      CLK_FREQ       => 100000000,
      BAUD_RATE      => 115200,
      RAM_ADDR_WIDTH => 24
    )
    port map (
      clk     => clk,
      rst     => rst,
      uart_tx => uart_tx,
      uart_rx => uart_rx
    );

  -- ========================================================================
  -- Reset sequence — assert for 10 cycles, then deassert
  -- ========================================================================
  rst_proc : process
  begin
    rst <= '1';
    wait for CLK_PERIOD * 10;
    rst <= '0';
    wait;
  end process rst_proc;

  -- ========================================================================
  -- Cycle counter + timeout
  -- ========================================================================
  counter_proc : process(clk)
  begin
    if rising_edge(clk) then
      cycle_count <= cycle_count + 1;
      if cycle_count >= MAX_CYCLES then
        report "TB: MAX_CYCLES (" & integer'image(MAX_CYCLES) &
               ") reached -- timeout" severity failure;
      end if;
    end if;
  end process counter_proc;

  -- ========================================================================
  -- UART TX monitor — detect any falling edge (start bit)
  -- ========================================================================
  uart_monitor : process(clk)
  begin
    if rising_edge(clk) then
      uart_tx_prev <= uart_tx;
      if uart_tx_prev = '1' and uart_tx = '0' then
        uart_activity <= true;
        report "TB: UART TX start bit detected at cycle " &
               integer'image(cycle_count) severity note;
      end if;
    end if;
  end process uart_monitor;

end architecture sim;
