library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

entity addition_demo is
    port (
        a   : in  std_logic_vector(3 downto 0);
        b   : in  std_logic_vector(3 downto 0);
        sum : out std_logic_vector(4 downto 0)
    );
end entity addition_demo;

architecture rtl of addition_demo is
begin
    sum <= std_logic_vector(resize(unsigned(a), 5) + resize(unsigned(b), 5));
end architecture rtl;

