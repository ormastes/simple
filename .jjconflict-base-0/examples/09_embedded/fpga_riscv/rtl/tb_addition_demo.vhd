library ieee;
use ieee.std_logic_1164.all;

entity tb_addition_demo is
end entity tb_addition_demo;

architecture sim of tb_addition_demo is
    signal a   : std_logic_vector(3 downto 0) := (others => '0');
    signal b   : std_logic_vector(3 downto 0) := (others => '0');
    signal sum : std_logic_vector(4 downto 0);
begin
    dut : entity work.addition_demo
        port map (
            a   => a,
            b   => b,
            sum => sum
        );

    process
    begin
        a <= "0011";
        b <= "0101";
        wait for 10 ns;
        assert sum = "01000" report "3 + 5 should equal 8" severity failure;

        a <= "1111";
        b <= "0001";
        wait for 10 ns;
        assert sum = "10000" report "15 + 1 should equal 16" severity failure;

        report "addition_demo PASS";
        wait;
    end process;
end architecture sim;

