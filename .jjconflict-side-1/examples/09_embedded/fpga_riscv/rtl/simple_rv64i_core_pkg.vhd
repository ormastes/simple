library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

package simple_rv64i_core_pkg is
    subtype rv64_word_t is std_logic_vector(63 downto 0);
    subtype rv32_word_t is std_logic_vector(31 downto 0);
end package simple_rv64i_core_pkg;
