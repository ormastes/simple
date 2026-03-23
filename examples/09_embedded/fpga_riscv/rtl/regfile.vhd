-- RV32I Register File - 32 x 32-bit registers
-- x0 is hardwired to zero

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

entity regfile is
    port (
        clk     : in  std_logic;
        -- Read ports
        rs1_addr : in  std_logic_vector(4 downto 0);
        rs2_addr : in  std_logic_vector(4 downto 0);
        rs1_data : out std_logic_vector(31 downto 0);
        rs2_data : out std_logic_vector(31 downto 0);
        -- Write port
        rd_addr  : in  std_logic_vector(4 downto 0);
        rd_data  : in  std_logic_vector(31 downto 0);
        rd_we    : in  std_logic
    );
end entity regfile;

architecture rtl of regfile is
    type reg_array_t is array (0 to 31) of std_logic_vector(31 downto 0);
    signal regs : reg_array_t := (
        2      => x"00000FFC",  -- SP (x2) = top of 4KB DMEM
        others => (others => '0')
    );
begin
    -- Async read (combinational)
    rs1_data <= (others => '0') when unsigned(rs1_addr) = 0
                else regs(to_integer(unsigned(rs1_addr)));
    rs2_data <= (others => '0') when unsigned(rs2_addr) = 0
                else regs(to_integer(unsigned(rs2_addr)));

    -- Sync write
    process(clk)
    begin
        if rising_edge(clk) then
            if rd_we = '1' and unsigned(rd_addr) /= 0 then
                regs(to_integer(unsigned(rd_addr))) <= rd_data;
            end if;
        end if;
    end process;
end architecture rtl;
