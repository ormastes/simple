-- sba_test_mem.vhd — Stage-5 SBA testbench bus target: 64 x 64-bit word
-- memory on the DM system-bus master port handshake (re/we held level with
-- addr/wdata/size until ack pulses for one clock; err sampled with ack).
--
-- Behavior:
--   * ACK_DELAY generic: cycles of re/we held before the single-cycle ack
--     (models a slow bus so SBCS.sbbusy has a real window).
--   * Address map: 64 words of 8 bytes, byte addresses 0x000..0x1FF.
--     addr(8 downto 3) selects the word.
--   * size = "11" (64-bit): full-word access, rdata(63:0) / wdata(63:0).
--   * size = "10" (32-bit): addr(2) selects the word half; reads return the
--     selected half in rdata(31:0), writes replace only that half.
--   * Any other size, an unaligned address (per size), or a byte address
--     >= 0x200 acks with err = '1' and does not touch memory.
--   * Initial contents: word(i) = x"A5A5_0000_0000_0000" + i * 0x1_0001
--     (distinct, easy to eyeball in hex).

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

entity sba_test_mem is
  generic (
    ACK_DELAY : natural := 8
  );
  port (
    clk   : in  std_logic;
    rst_n : in  std_logic;

    sb_re_i    : in  std_logic;
    sb_we_i    : in  std_logic;
    sb_addr_i  : in  std_logic_vector(63 downto 0);
    sb_wdata_i : in  std_logic_vector(63 downto 0);
    sb_size_i  : in  std_logic_vector(1 downto 0);
    sb_rdata_o : out std_logic_vector(63 downto 0);
    sb_ack_o   : out std_logic;
    sb_err_o   : out std_logic
  );
end entity sba_test_mem;

architecture rtl of sba_test_mem is

  type mem_t is array (0 to 63) of std_logic_vector(63 downto 0);

  function init_mem return mem_t is
    variable m : mem_t;
  begin
    for i in 0 to 63 loop
      m(i) := std_logic_vector(
                x"A5A5000000000000" + to_unsigned(i * 16#10001#, 64));
    end loop;
    return m;
  end function init_mem;

  signal mem : mem_t := init_mem;

  signal ack_r   : std_logic := '0';
  signal err_r   : std_logic := '0';
  signal rdata_r : std_logic_vector(63 downto 0) := (others => '0');

begin

  process (clk, rst_n)
    variable cnt  : natural := 0;
    variable widx : natural;
    variable bad  : boolean;
  begin
    if rst_n = '0' then
      ack_r   <= '0';
      err_r   <= '0';
      rdata_r <= (others => '0');
      cnt := 0;
    elsif rising_edge(clk) then
      ack_r <= '0';
      err_r <= '0';
      if (sb_re_i = '1' or sb_we_i = '1') and ack_r = '0' then
        if cnt = ACK_DELAY then
          cnt := 0;
          ack_r <= '1';
          bad := unsigned(sb_addr_i) >= 16#200#
                 or (sb_size_i = "11" and sb_addr_i(2 downto 0) /= "000")
                 or (sb_size_i = "10" and sb_addr_i(1 downto 0) /= "00")
                 or (sb_size_i /= "11" and sb_size_i /= "10");
          if bad then
            err_r <= '1';
          else
            widx := to_integer(unsigned(sb_addr_i(8 downto 3)));
            if sb_size_i = "11" then          -- 64-bit
              if sb_we_i = '1' then
                mem(widx) <= sb_wdata_i;
              else
                rdata_r <= mem(widx);
              end if;
            else                              -- 32-bit half select
              if sb_we_i = '1' then
                if sb_addr_i(2) = '1' then
                  mem(widx)(63 downto 32) <= sb_wdata_i(31 downto 0);
                else
                  mem(widx)(31 downto 0) <= sb_wdata_i(31 downto 0);
                end if;
              else
                rdata_r <= (others => '0');
                if sb_addr_i(2) = '1' then
                  rdata_r(31 downto 0) <= mem(widx)(63 downto 32);
                else
                  rdata_r(31 downto 0) <= mem(widx)(31 downto 0);
                end if;
              end if;
            end if;
          end if;
        else
          cnt := cnt + 1;
        end if;
      else
        cnt := 0;
      end if;
    end if;
  end process;

  sb_rdata_o <= rdata_r;
  sb_ack_o   <= ack_r;
  sb_err_o   <= err_r;

end architecture rtl;
