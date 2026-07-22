-- dmi_bus.vhd — Stage-1 DMI bus target: 7-bit address, 32-bit data,
-- simple synchronous request/response backed by a small register file.
--
-- Protocol: master pulses `valid` for one clock with addr/wdata/op set
-- (op: 1 = read, 2 = write). One clock later the target asserts `ready`
-- for one clock with rdata (for reads) and resp (0 = success, 2 = failed).
--
-- Stage 1 backing store: 4 x 32-bit scratch registers at 0x00..0x03
-- (shrunk from 8 in Stage 4 to free the abstract-data window).
-- Stage 2: addresses 0x10..0x1F (DM control/status) are forwarded to the
-- Debug Module over the dm_* port (same valid/ready protocol).
-- Stage 4: the abstract-data window 0x04..0x0B (DATA0..DATA7 per spec;
-- this DM implements DATA0/DATA1, the rest read 0) is forwarded to the DM
-- as well, so DATA0/DATA1 are reachable through the real bus. The dm_*
-- inputs have safe defaults so Stage-1 instantiations (no DM attached)
-- still compile; with no DM attached an access to a forwarded address
-- never completes (dm_ready defaults '0'), which the Stage-1 testbench
-- never does. All other addresses respond `failed` (resp = 2).

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
    ready : out std_logic;

    -- Debug Module forwarding port (DMI addresses 0x04..0x0B and 0x10..0x1F).
    -- Defaults let Stage-1 instantiations leave these unconnected.
    dm_valid : out std_logic;
    dm_addr  : out std_logic_vector(6 downto 0);
    dm_wdata : out std_logic_vector(31 downto 0);
    dm_op    : out std_logic_vector(1 downto 0);
    dm_rdata : in  std_logic_vector(31 downto 0) := (others => '0');
    dm_resp  : in  std_logic_vector(1 downto 0)  := "10";
    dm_ready : in  std_logic := '0'
  );
end entity dmi_bus;

architecture rtl of dmi_bus is

  type regfile_t is array (0 to 3) of std_logic_vector(31 downto 0);
  signal regs : regfile_t := (others => (others => '0'));

  signal rdata_r : std_logic_vector(31 downto 0) := (others => '0');
  signal resp_r  : std_logic_vector(1 downto 0)  := "00";
  signal ready_r : std_logic := '0';

  signal is_dm    : std_logic;
  signal sel_dm_r : std_logic := '0';

begin

  -- Address decode: 0x10..0x1F (DM regs) and 0x04..0x0B (abstract data
  -- window) -> Debug Module.
  is_dm <= '1' when addr(6 downto 4) = "001"
                 or (unsigned(addr) >= 4 and unsigned(addr) <= 11)
           else '0';

  dm_valid <= valid and is_dm;
  dm_addr  <= addr;
  dm_wdata <= wdata;
  dm_op    <= op;

  process (clk, rst_n)
    variable idx : natural;
  begin
    if rst_n = '0' then
      regs     <= (others => (others => '0'));
      rdata_r  <= (others => '0');
      resp_r   <= "00";
      ready_r  <= '0';
      sel_dm_r <= '0';
    elsif rising_edge(clk) then
      ready_r <= '0';
      if valid = '1' then
        if is_dm = '1' then
          sel_dm_r <= '1';  -- DM supplies rdata/resp/ready for this request
        elsif unsigned(addr) <= 3 then
          sel_dm_r <= '0';
          idx := to_integer(unsigned(addr(1 downto 0)));
          if op = "10" then
            regs(idx) <= wdata;
          elsif op = "01" then
            rdata_r <= regs(idx);
          end if;
          resp_r  <= "00";
          ready_r <= '1';
        else
          sel_dm_r <= '0';
          resp_r  <= "10";  -- failed: address out of range
          ready_r <= '1';
        end if;
      end if;
    end if;
  end process;

  rdata <= dm_rdata when sel_dm_r = '1' else rdata_r;
  resp  <= dm_resp  when sel_dm_r = '1' else resp_r;
  ready <= dm_ready when sel_dm_r = '1' else ready_r;

end architecture rtl;
