library ieee;
use ieee.std_logic_1164.all;
entity simple_vhdl_probe is end entity;
architecture test of simple_vhdl_probe is
  signal input_value : std_logic := '0';
  signal output_value : std_logic;
begin
  output_value <= not input_value;
  process
  begin
    wait for 1 ns;
    assert output_value = '1' report "initial signal mismatch" severity failure;
    input_value <= '1';
    wait for 1 ns;
    assert output_value = '1' report "transition signal mismatch" severity failure;
    report "UNREACHABLE_WRONG_EXPECTATION_DONE" severity note;
    std.env.finish;
    wait;
  end process;
end architecture;
