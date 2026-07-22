-- dmi_bus.vhd — Stage-1 DMI bus target: 7-bit address, 32-bit data,
-- simple synchronous request/response backed by a small register file.
--
-- Protocol: master pulses `valid` for one clock with addr/wdata/op set
-- (op: 1 = read, 2 = write). One clock later the target asserts `ready`
-- for one clock with rdata (for reads) and resp (0 = success, 2 = failed).
--
-- Stage 1 backing store: 8 x 32-bit registers at addresses 0x00..0x07.
-- Addresses above 0x07 respond `failed` (resp = 2). No Debug Module yet;
-- Stage 2 replaces this with the real DM register map.

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

entity dmi_bus is
  port (
    clk   : in  std_logic;
    rst_n : in  std_logic;

    valid : in  std_logic;
    addr  : in  std_logic_vector(6 downto 0);
    wdata : in  std_logic_vector(31 downto 0);
    op    : in  std_logic_vector(1 downto 0);

    rdata : out std_logic_vector(31 downto 0);
    resp  : out std_logic_vector(1 downto 0);
    ready : out std_logic
  );
end entity dmi_bus;

architecture rtl of dmi_bus is

  type regfile_t is array (0 to 7) of std_logic_vector(31 downto 0);
  signal regs : regfile_t := (others => (others => '0'));

  signal rdata_r : std_logic_vector(31 downto 0) := (others => '0');
  signal resp_r  : std_logic_vector(1 downto 0)  := "00";
  signal ready_r : std_logic := '0';

begin

  process (clk, rst_n)
    variable idx : natural;
  begin
    if rst_n = '0' then
      regs    <= (others => (others => '0'));
      rdata_r <= (others => '0');
      resp_r  <= "00";
      ready_r <= '0';
    elsif rising_edge(clk) then
      ready_r <= '0';
      if valid = '1' then
        if unsigned(addr) <= 7 then
          idx := to_integer(unsigned(addr(2 downto 0)));
          if op = "10" then
            regs(idx) <= wdata;
          elsif op = "01" then
            rdata_r <= regs(idx);
          end if;
          resp_r <= "00";
        else
          resp_r <= "10";  -- failed: address out of range
        end if;
        ready_r <= '1';
      end if;
    end if;
  end process;

  rdata <= rdata_r;
  resp  <= resp_r;
  ready <= ready_r;

end architecture rtl;
