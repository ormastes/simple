-- RISC-V ISA gate: sample UART pass/fail char to determine test result
-- Tests write 'P' to UART MMIO 0x10000000 for pass, 'F' for fail, then j .
library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use std.textio.all;

entity tb_gate is end entity;

architecture sim of tb_gate is
  signal clk : std_logic := '0';
  signal rst : std_logic := '1';
  signal uart_tx : std_logic;
  signal dv : std_logic;
  signal dbyte : std_logic_vector(7 downto 0);
  signal dpc : std_logic_vector(15 downto 0);
  signal dins : std_logic_vector(31 downto 0);
  signal da0 : std_logic_vector(7 downto 0);
  signal dra : std_logic_vector(15 downto 0);
  signal dsp : std_logic_vector(15 downto 0);
  signal dph : std_logic_vector(3 downto 0);

  signal prev_dv : std_logic := '0';
  signal result_seen : std_logic := '0';
begin
  dut: entity work.rv32_exec_core
    generic map (CLK_FREQ => 100000000, BAUD_RATE => 115200)
    port map (clk=>clk, rst=>rst, uart_tx=>uart_tx,
              debug_uart_valid=>dv, debug_uart_byte=>dbyte, debug_pc=>dpc,
              debug_ins=>dins, debug_a0=>da0, debug_ra=>dra, debug_sp=>dsp, debug_phase=>dph);

  clk <= not clk after 5 ns;

  process(clk)
    variable l : line;
  begin
    if rising_edge(clk) then
      if rst='0' and result_seen='0' then
        -- Look for UART byte on rising edge of debug_uart_valid
        if dv='1' and prev_dv='0' then
          -- Check for 'P' (0x50) or 'F' (0x46)
          if dbyte = x"50" then
            write(l, string'("GATE_RESULT=PASS"));
            writeline(output, l);
            result_seen <= '1';
          elsif dbyte = x"46" then
            write(l, string'("GATE_RESULT=FAIL"));
            writeline(output, l);
            result_seen <= '1';
          end if;
        end if;
        prev_dv <= dv;
      end if;
    end if;
  end process;

  rst <= '1', '0' after 20 ns;
end architecture;
