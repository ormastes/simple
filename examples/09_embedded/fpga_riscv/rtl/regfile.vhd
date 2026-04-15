library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

entity regfile is
    port (
        clk      : in  std_logic;
        rs1_addr : in  std_logic_vector(4 downto 0);
        rs2_addr : in  std_logic_vector(4 downto 0);
        rs1_data : out std_logic_vector(31 downto 0);
        rs2_data : out std_logic_vector(31 downto 0);
        rd_addr  : in  std_logic_vector(4 downto 0);
        rd_data  : in  std_logic_vector(31 downto 0);
        rd_we    : in  std_logic;
        -- Direct read of a0 (x10) and a1 (x11) for semihosting
        a0_out   : out std_logic_vector(31 downto 0);
        a1_out   : out std_logic_vector(31 downto 0)
    );
end entity regfile;

architecture rtl of regfile is
    type reg_array_t is array (0 to 31) of std_logic_vector(31 downto 0);
    signal regs : reg_array_t := (
        2      => x"00000FFC",  -- SP = top of 4KB DMEM
        others => (others => '0')
    );
begin
    rs1_data <= (others => '0') when unsigned(rs1_addr) = 0
                else regs(to_integer(unsigned(rs1_addr)));
    rs2_data <= (others => '0') when unsigned(rs2_addr) = 0
                else regs(to_integer(unsigned(rs2_addr)));
    a0_out <= regs(10);  -- x10 = a0
    a1_out <= regs(11);  -- x11 = a1

    process(clk)
    begin
        if rising_edge(clk) then
            if rd_we = '1' and unsigned(rd_addr) /= 0 then
                regs(to_integer(unsigned(rd_addr))) <= rd_data;
            end if;
        end if;
    end process;
end architecture rtl;
