library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use work.rv32i_pkg.all;

entity decoder is
    port (
        instruction : in  std_logic_vector(31 downto 0);
        opcode      : out std_logic_vector(6 downto 0);
        rd          : out std_logic_vector(4 downto 0);
        rs1         : out std_logic_vector(4 downto 0);
        rs2         : out std_logic_vector(4 downto 0);
        funct3      : out std_logic_vector(2 downto 0);
        funct7      : out std_logic_vector(6 downto 0);
        imm         : out std_logic_vector(31 downto 0);
        alu_op      : out alu_op_t;
        reg_write   : out std_logic;
        mem_read    : out std_logic;
        mem_write   : out std_logic;
        mem_to_reg  : out std_logic;
        alu_src     : out std_logic;
        branch      : out std_logic;
        jump        : out std_logic
    );
end entity decoder;

architecture rtl of decoder is
    signal op : std_logic_vector(6 downto 0);
    signal f3 : std_logic_vector(2 downto 0);
    signal f7 : std_logic_vector(6 downto 0);
begin
    op <= instruction(6 downto 0);
    f3 <= instruction(14 downto 12);
    f7 <= instruction(31 downto 25);
    opcode <= op; rd <= instruction(11 downto 7);
    rs1 <= instruction(19 downto 15); rs2 <= instruction(24 downto 20);
    funct3 <= f3; funct7 <= f7;

    process(instruction, op)
    begin
        case op is
            when OP_IMMED | OP_LOAD | OP_JALR =>
                imm <= (31 downto 12 => instruction(31)) & instruction(31 downto 20);
            when OP_STORE =>
                imm <= (31 downto 12 => instruction(31)) & instruction(31 downto 25) & instruction(11 downto 7);
            when OP_BRANCH =>
                imm <= (31 downto 13 => instruction(31)) & instruction(31) & instruction(7) & instruction(30 downto 25) & instruction(11 downto 8) & '0';
            when OP_LUI | OP_AUIPC =>
                imm <= instruction(31 downto 12) & x"000";
            when OP_JAL =>
                imm <= (31 downto 21 => instruction(31)) & instruction(31) & instruction(19 downto 12) & instruction(20) & instruction(30 downto 21) & '0';
            when others =>
                imm <= (others => '0');
        end case;
    end process;

    process(op, f3, f7)
    begin
        alu_op <= ALU_ADD;
        case op is
            when OP_REG =>
                case f3 is
                    when "000" => if f7(5) = '1' then alu_op <= ALU_SUB; else alu_op <= ALU_ADD; end if;
                    when "001" => alu_op <= ALU_SLL;
                    when "010" => alu_op <= ALU_SLT;
                    when "011" => alu_op <= ALU_SLTU;
                    when "100" => alu_op <= ALU_XOR;
                    when "101" => if f7(5) = '1' then alu_op <= ALU_SRA; else alu_op <= ALU_SRL; end if;
                    when "110" => alu_op <= ALU_OR;
                    when "111" => alu_op <= ALU_AND;
                    when others => null;
                end case;
            when OP_IMMED =>
                case f3 is
                    when "000" => alu_op <= ALU_ADD;
                    when "001" => alu_op <= ALU_SLL;
                    when "010" => alu_op <= ALU_SLT;
                    when "011" => alu_op <= ALU_SLTU;
                    when "100" => alu_op <= ALU_XOR;
                    when "101" => if f7(5) = '1' then alu_op <= ALU_SRA; else alu_op <= ALU_SRL; end if;
                    when "110" => alu_op <= ALU_OR;
                    when "111" => alu_op <= ALU_AND;
                    when others => null;
                end case;
            when OP_LUI => alu_op <= ALU_PASS_B;
            when others => alu_op <= ALU_ADD;
        end case;
    end process;

    reg_write  <= '1' when (op = OP_REG or op = OP_IMMED or op = OP_LOAD or
                            op = OP_LUI or op = OP_AUIPC or op = OP_JAL or op = OP_JALR) else '0';
    mem_read   <= '1' when op = OP_LOAD  else '0';
    mem_write  <= '1' when op = OP_STORE else '0';
    mem_to_reg <= '1' when op = OP_LOAD  else '0';
    alu_src    <= '1' when (op = OP_IMMED or op = OP_LOAD or op = OP_STORE or
                            op = OP_LUI or op = OP_AUIPC or op = OP_JAL or op = OP_JALR) else '0';
    branch     <= '1' when op = OP_BRANCH else '0';
    jump       <= '1' when (op = OP_JAL or op = OP_JALR) else '0';
end architecture rtl;
