-- RV32I ALU - Arithmetic Logic Unit

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use work.rv32i_pkg.all;

entity alu is
    port (
        op_a   : in  std_logic_vector(31 downto 0);
        op_b   : in  std_logic_vector(31 downto 0);
        alu_op : in  alu_op_t;
        result : out std_logic_vector(31 downto 0);
        zero   : out std_logic
    );
end entity alu;

architecture rtl of alu is
    signal res_i : std_logic_vector(31 downto 0);
begin
    process(op_a, op_b, alu_op)
        variable shamt : natural;
    begin
        shamt := to_integer(unsigned(op_b(4 downto 0)));
        case alu_op is
            when ALU_ADD   => res_i <= std_logic_vector(signed(op_a) + signed(op_b));
            when ALU_SUB   => res_i <= std_logic_vector(signed(op_a) - signed(op_b));
            when ALU_SLL   => res_i <= std_logic_vector(shift_left(unsigned(op_a), shamt));
            when ALU_SLT   => res_i <= x"00000001" when signed(op_a) < signed(op_b) else x"00000000";
            when ALU_SLTU  => res_i <= x"00000001" when unsigned(op_a) < unsigned(op_b) else x"00000000";
            when ALU_XOR   => res_i <= op_a xor op_b;
            when ALU_SRL   => res_i <= std_logic_vector(shift_right(unsigned(op_a), shamt));
            when ALU_SRA   => res_i <= std_logic_vector(shift_right(signed(op_a), shamt));
            when ALU_OR    => res_i <= op_a or op_b;
            when ALU_AND   => res_i <= op_a and op_b;
            when ALU_PASS_B => res_i <= op_b;
        end case;
    end process;

    result <= res_i;
    zero   <= '1' when res_i = x"00000000" else '0';
end architecture rtl;
