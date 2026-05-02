-- generated-from: simple_rv64gc_core.spl
-- source-map: Rv64Instruction.opcode => imem_rdata(6 downto 0)
-- source-map: Rv64Instruction.rd => imem_rdata(11 downto 7)
-- source-map: Rv64Instruction.funct3 => imem_rdata(14 downto 12)
-- source-map: Rv64Instruction.rs1 => imem_rdata(19 downto 15)
-- source-map: Rv64Instruction.rs2 => imem_rdata(24 downto 20)
-- source-map: Rv64Instruction.funct7 => imem_rdata(31 downto 25)
-- source-map: RiscvBranchEncoding.bit11 => imem_rdata(7 downto 7)
-- source-map: RiscvBranchEncoding.low => imem_rdata(11 downto 8)
-- source-map: RiscvBranchEncoding.high => imem_rdata(30 downto 25)
-- source-map: RiscvBranchEncoding.bit12 => imem_rdata(31 downto 31)
-- source-map: RiscvStoreEncoding.low => imem_rdata(11 downto 7)
-- source-map: RiscvStoreEncoding.high => imem_rdata(31 downto 25)
-- source-map: RiscvIImmediateEncoding.value => imem_rdata(31 downto 20)
-- source-map: RiscvUpperImmediateEncoding.high20 => imem_rdata(31 downto 12)
-- source-map: RiscvExecuteControlEncoding.funct3 => imem_rdata(14 downto 12)
-- source-map: RiscvExecuteControlEncoding.shamt_low5 => imem_rdata(24 downto 20)
-- source-map: RiscvExecuteControlEncoding.shamt_bit5 => imem_rdata(25 downto 25)
-- source-map: RiscvExecuteControlEncoding.bit30 => imem_rdata(30 downto 30)
-- source-map: RiscvExecuteDatapathEncoding.opcode => imem_rdata(6 downto 0)
-- source-map: RiscvExecuteDatapathEncoding.funct3 => imem_rdata(14 downto 12)
-- source-map: RiscvExecuteDatapathEncoding.bit30 => imem_rdata(30 downto 30)
-- source-map: RiscvBranchDatapathEncoding.opcode => imem_rdata(6 downto 0)
-- source-map: RiscvBranchDatapathEncoding.funct3 => imem_rdata(14 downto 12)
-- source-map: RiscvControlFlowDatapathEncoding.opcode => imem_rdata(6 downto 0)
-- source-map: RiscvMemoryAccessControlEncoding.funct3 => imem_rdata(14 downto 12)
-- source-map: RiscvJumpEncoding.high8 => imem_rdata(19 downto 12)
-- source-map: RiscvJumpEncoding.bit11 => imem_rdata(20 downto 20)
-- source-map: RiscvJumpEncoding.low10 => imem_rdata(30 downto 21)
-- source-map: RiscvJumpEncoding.bit20 => imem_rdata(31 downto 31)
-- source-map: RiscvDispatchClassEncoding.opcode => imem_rdata(6 downto 0)
-- source-map: RiscvTrapHaltControlEncoding.opcode => imem_rdata(6 downto 0)
-- proof-lane: generated_rv64_linux shell=none
-- readiness: contract linux-boot-validated=false

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

package simple_rv64i_core_pkg is
    constant XLEN : natural := 64;
    subtype xword_t is std_logic_vector(XLEN - 1 downto 0);
    constant RESET_VECTOR : xword_t := x"0000000080000000";
    constant BOOT_STRIDE : natural := 4;
    function rv64c_is_compressed(instr : std_logic_vector(31 downto 0)) return boolean;
    function rv64c_decompress(instr : std_logic_vector(15 downto 0)) return std_logic_vector;
end package simple_rv64i_core_pkg;

package body simple_rv64i_core_pkg is
    function sign_extend(bits : std_logic_vector; width : natural) return std_logic_vector is
        variable result : std_logic_vector(width - 1 downto 0);
    begin
        result := std_logic_vector(resize(signed(bits), width));
        return result;
    end function;

    function encode_r(opcode : std_logic_vector(6 downto 0); rd : natural; funct3 : std_logic_vector(2 downto 0); rs1 : natural; rs2 : natural; funct7 : std_logic_vector(6 downto 0)) return std_logic_vector is
    begin
        return funct7 & std_logic_vector(to_unsigned(rs2, 5)) & std_logic_vector(to_unsigned(rs1, 5)) & funct3 & std_logic_vector(to_unsigned(rd, 5)) & opcode;
    end function;

    function encode_i(opcode : std_logic_vector(6 downto 0); rd : natural; funct3 : std_logic_vector(2 downto 0); rs1 : natural; imm : std_logic_vector(11 downto 0)) return std_logic_vector is
    begin
        return imm & std_logic_vector(to_unsigned(rs1, 5)) & funct3 & std_logic_vector(to_unsigned(rd, 5)) & opcode;
    end function;

    function encode_s(opcode : std_logic_vector(6 downto 0); funct3 : std_logic_vector(2 downto 0); rs1 : natural; rs2 : natural; imm : std_logic_vector(11 downto 0)) return std_logic_vector is
    begin
        return imm(11 downto 5) & std_logic_vector(to_unsigned(rs2, 5)) & std_logic_vector(to_unsigned(rs1, 5)) & funct3 & imm(4 downto 0) & opcode;
    end function;

    function encode_b(opcode : std_logic_vector(6 downto 0); funct3 : std_logic_vector(2 downto 0); rs1 : natural; rs2 : natural; imm : std_logic_vector(12 downto 0)) return std_logic_vector is
    begin
        return imm(12) & imm(10 downto 5) & std_logic_vector(to_unsigned(rs2, 5)) & std_logic_vector(to_unsigned(rs1, 5)) & funct3 & imm(4 downto 1) & imm(11) & opcode;
    end function;

    function encode_u(opcode : std_logic_vector(6 downto 0); rd : natural; imm : std_logic_vector(19 downto 0)) return std_logic_vector is
    begin
        return imm & std_logic_vector(to_unsigned(rd, 5)) & opcode;
    end function;

    function encode_j(opcode : std_logic_vector(6 downto 0); rd : natural; imm : std_logic_vector(20 downto 0)) return std_logic_vector is
    begin
        return imm(20) & imm(10 downto 1) & imm(11) & imm(19 downto 12) & std_logic_vector(to_unsigned(rd, 5)) & opcode;
    end function;

    function rvc_reg(bits : std_logic_vector(2 downto 0)) return natural is
    begin
        return 8 + to_integer(unsigned(bits));
    end function;

    function rv64c_is_compressed(instr : std_logic_vector(31 downto 0)) return boolean is
    begin
        return instr(1 downto 0) /= "11";
    end function;

    function rv64c_decompress(instr : std_logic_vector(15 downto 0)) return std_logic_vector is
        variable result : std_logic_vector(31 downto 0) := (others => '0');
        variable funct3 : std_logic_vector(2 downto 0);
        variable funct2 : std_logic_vector(1 downto 0);
        variable funct2b : std_logic_vector(1 downto 0);
        variable rd : natural;
        variable rs1_c : natural;
        variable rs2_c : natural;
        variable rs2 : natural;
        variable imm12 : std_logic_vector(11 downto 0);
        variable imm13 : std_logic_vector(12 downto 0);
        variable imm20 : std_logic_vector(19 downto 0);
        variable imm21 : std_logic_vector(20 downto 0);
        variable shamt6 : std_logic_vector(5 downto 0);
    begin
        funct3 := instr(15 downto 13);
        case instr(1 downto 0) is
            when "00" =>
                case funct3 is
                    when "000" =>
                        imm12 := "00" & instr(10 downto 7) & instr(12 downto 11) & instr(5) & instr(6) & "00";
                        if imm12 = x"000" then
                            return x"00000000";
                        end if;
                        rd := rvc_reg(instr(4 downto 2));
                        return encode_i("0010011", rd, "000", 2, imm12);
                    when "010" =>
                        imm12 := "00000" & instr(5) & instr(12 downto 10) & instr(6) & "00";
                        rd := rvc_reg(instr(4 downto 2));
                        rs1_c := rvc_reg(instr(9 downto 7));
                        return encode_i("0000011", rd, "010", rs1_c, imm12);
                    when "011" =>
                        imm12 := "0000" & instr(6 downto 5) & instr(12 downto 10) & "000";
                        rd := rvc_reg(instr(4 downto 2));
                        rs1_c := rvc_reg(instr(9 downto 7));
                        return encode_i("0000011", rd, "011", rs1_c, imm12);
                    when "110" =>
                        imm12 := "00000" & instr(5) & instr(12 downto 10) & instr(6) & "00";
                        rs2_c := rvc_reg(instr(4 downto 2));
                        rs1_c := rvc_reg(instr(9 downto 7));
                        return encode_s("0100011", "010", rs1_c, rs2_c, imm12);
                    when "111" =>
                        imm12 := "0000" & instr(6 downto 5) & instr(12 downto 10) & "000";
                        rs2_c := rvc_reg(instr(4 downto 2));
                        rs1_c := rvc_reg(instr(9 downto 7));
                        return encode_s("0100011", "011", rs1_c, rs2_c, imm12);
                    when others =>
                        return x"00000000";
                end case;
            when "01" =>
                case funct3 is
                    when "000" =>
                        rd := to_integer(unsigned(instr(11 downto 7)));
                        imm12 := sign_extend(instr(12) & instr(6 downto 2), 12);
                        return encode_i("0010011", rd, "000", rd, imm12);
                    when "001" =>
                        rd := to_integer(unsigned(instr(11 downto 7)));
                        if rd = 0 then
                            return x"00000000";
                        end if;
                        imm12 := sign_extend(instr(12) & instr(6 downto 2), 12);
                        return encode_i("0011011", rd, "000", rd, imm12);
                    when "010" =>
                        rd := to_integer(unsigned(instr(11 downto 7)));
                        imm12 := sign_extend(instr(12) & instr(6 downto 2), 12);
                        return encode_i("0010011", rd, "000", 0, imm12);
                    when "011" =>
                        rd := to_integer(unsigned(instr(11 downto 7)));
                        if rd = 2 then
                            imm12 := sign_extend(instr(12) & instr(4) & instr(3) & instr(5) & instr(2) & instr(6) & "0000", 12);
                            if imm12 = x"000" then
                                return x"00000000";
                            end if;
                            return encode_i("0010011", 2, "000", 2, imm12);
                        end if;
                        imm20 := instr(12) & instr(12) & instr(12) & instr(6 downto 2) & "000000000000";
                        if imm20 = x"00000" then
                            return x"00000000";
                        end if;
                        return encode_u("0110111", rd, imm20);
                    when "100" =>
                        funct2 := instr(11 downto 10);
                        rd := rvc_reg(instr(9 downto 7));
                        case funct2 is
                            when "00" =>
                                shamt6 := instr(12) & instr(6 downto 2);
                                return encode_i("0010011", rd, "101", rd, "000000" & shamt6);
                            when "01" =>
                                shamt6 := instr(12) & instr(6 downto 2);
                                return encode_i("0010011", rd, "101", rd, "010000" & shamt6);
                            when "10" =>
                                imm12 := sign_extend(instr(12) & instr(6 downto 2), 12);
                                return encode_i("0010011", rd, "111", rd, imm12);
                            when others =>
                                rs2_c := rvc_reg(instr(4 downto 2));
                                funct2b := instr(6 downto 5);
                                if instr(12) = '0' then
                                    case funct2b is
                                        when "00" => return encode_r("0110011", rd, "000", rd, rs2_c, "0100000");
                                        when "01" => return encode_r("0110011", rd, "100", rd, rs2_c, "0000000");
                                        when "10" => return encode_r("0110011", rd, "110", rd, rs2_c, "0000000");
                                        when "11" => return encode_r("0110011", rd, "111", rd, rs2_c, "0000000");
                                        when others => return x"00000000";
                                    end case;
                                end if;
                                case funct2b is
                                    when "00" => return encode_r("0111011", rd, "000", rd, rs2_c, "0100000");
                                    when "01" => return encode_r("0111011", rd, "000", rd, rs2_c, "0000000");
                                    when others => return x"00000000";
                                end case;
                        end case;
                    when "101" =>
                        imm21 := sign_extend(instr(12) & instr(8) & instr(10 downto 9) & instr(6) & instr(7) & instr(2) & instr(11) & instr(5 downto 3) & '0', 21);
                        return encode_j("1101111", 0, imm21);
                    when "110" =>
                        rs1_c := rvc_reg(instr(9 downto 7));
                        imm13 := sign_extend(instr(12) & instr(6 downto 5) & instr(2) & instr(11 downto 10) & instr(4 downto 3) & '0', 13);
                        return encode_b("1100011", "000", rs1_c, 0, imm13);
                    when "111" =>
                        rs1_c := rvc_reg(instr(9 downto 7));
                        imm13 := sign_extend(instr(12) & instr(6 downto 5) & instr(2) & instr(11 downto 10) & instr(4 downto 3) & '0', 13);
                        return encode_b("1100011", "001", rs1_c, 0, imm13);
                    when others =>
                        return x"00000000";
                end case;
            when "10" =>
                case funct3 is
                    when "000" =>
                        rd := to_integer(unsigned(instr(11 downto 7)));
                        if rd = 0 then
                            return x"00000000";
                        end if;
                        shamt6 := instr(12) & instr(6 downto 2);
                        return encode_i("0010011", rd, "001", rd, "000000" & shamt6);
                    when "010" =>
                        rd := to_integer(unsigned(instr(11 downto 7)));
                        if rd = 0 then
                            return x"00000000";
                        end if;
                        imm12 := "0000" & instr(3 downto 2) & instr(12) & instr(6 downto 4) & "00";
                        return encode_i("0000011", rd, "010", 2, imm12);
                    when "011" =>
                        rd := to_integer(unsigned(instr(11 downto 7)));
                        if rd = 0 then
                            return x"00000000";
                        end if;
                        imm12 := "000" & instr(4 downto 2) & instr(12) & instr(6 downto 5) & "000";
                        return encode_i("0000011", rd, "011", 2, imm12);
                    when "100" =>
                        rd := to_integer(unsigned(instr(11 downto 7)));
                        rs2 := to_integer(unsigned(instr(6 downto 2)));
                        if instr(12) = '0' then
                            if rs2 = 0 then
                                if rd = 0 then
                                    return x"00000000";
                                end if;
                                return encode_i("1100111", 0, "000", rd, x"000");
                            end if;
                            return encode_r("0110011", rd, "000", 0, rs2, "0000000");
                        elsif rs2 = 0 then
                            if rd = 0 then
                                return x"00100073";
                            end if;
                            return encode_i("1100111", 1, "000", rd, x"000");
                        else
                            return encode_r("0110011", rd, "000", rd, rs2, "0000000");
                        end if;
                    when "110" =>
                        rs2 := to_integer(unsigned(instr(6 downto 2)));
                        imm12 := "0000" & instr(8 downto 7) & instr(12 downto 9) & "00";
                        return encode_s("0100011", "010", 2, rs2, imm12);
                    when "111" =>
                        rs2 := to_integer(unsigned(instr(6 downto 2)));
                        imm12 := "000" & instr(9 downto 7) & instr(12 downto 10) & "000";
                        return encode_s("0100011", "011", 2, rs2, imm12);
                    when others =>
                        return x"00000000";
                end case;
            when others =>
                return x"00000000";
        end case;
    end function;
end package body simple_rv64i_core_pkg;
