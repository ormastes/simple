-- debug_registers.vhd — RISC-V Debug Spec v0.13 DM register block (Stage 2).
--
-- DMI slave for addresses 0x10..0x1F (same 1-cycle valid/ready protocol as
-- dmi_bus scratch): request sampled on the clock where dmi_valid = '1',
-- response (rdata/resp/ready) driven the following clock, ready for 1 clock.
--
-- Implemented registers:
--   0x10 DMCONTROL  — dmactive(0), ndmreset(1), ackhavereset(28, W1),
--                     resumereq(30, W1 pulse), haltreq(31, level).
--                     Single hart: hasel/hartsello/hartselhi ignored, read 0.
--                     haltreq/resumereq/ackhavereset are write-only (read 0)
--                     per spec field access "W".
--   0x11 DMSTATUS   — version=2 (0.13), authenticated=1 (no auth), and
--                     single-hart status: all==any for halted/running/
--                     resumeack/havereset.
--   0x12 HARTINFO   — all zero (nscratch=0, dataaccess=0, datasize=0).
--   0x16 ABSTRACTCS — zeros except cmderr(10:8); progbufsize=0, datacount=0
--                     (no abstract commands until Stage 3). cmderr is W1C.
--   0x17 COMMAND    — unimplemented: any write sets cmderr=2 (not supported),
--                     sticky (only set when cmderr was 0); reads as 0.
--   other 0x1x      — read 0 / write ignored, resp = success (harmless
--                     unimplemented optional registers: haltsum, hawindow...).
--
-- dmactive semantics: writing DMCONTROL with dmactive=0 resets ALL DM state.
-- While dmactive=0, DMCONTROL reads back 0 and all other write bits of the
-- activating write are ignored (fields take effect only once dmactive was
-- already 1 on a previous write) — debugger must write dmactive=1 first,
-- then issue requests, matching the spec's "poll until dmactive reads 1".

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

entity debug_registers is
  port (
    clk   : in  std_logic;
    rst_n : in  std_logic;

    -- DMI slave (forwarded 0x10..0x1F requests from dmi_bus)
    dmi_valid : in  std_logic;
    dmi_addr  : in  std_logic_vector(6 downto 0);
    dmi_wdata : in  std_logic_vector(31 downto 0);
    dmi_op    : in  std_logic_vector(1 downto 0);
    dmi_rdata : out std_logic_vector(31 downto 0);
    dmi_resp  : out std_logic_vector(1 downto 0);
    dmi_ready : out std_logic;

    -- Control outputs to the DM core state machine
    dmactive_o        : out std_logic;
    ndmreset_o        : out std_logic;
    haltreq_o         : out std_logic;  -- level, as written to DMCONTROL.haltreq
    resumereq_pulse_o : out std_logic;  -- 1-clock pulse per resumereq=1 write

    -- Status inputs (from DM core / hart)
    halted_i    : in  std_logic;
    running_i   : in  std_logic;
    resumeack_i : in  std_logic
  );
end entity debug_registers;

architecture rtl of debug_registers is

  constant A_DMCONTROL  : std_logic_vector(6 downto 0) := "0010000";  -- 0x10
  constant A_DMSTATUS   : std_logic_vector(6 downto 0) := "0010001";  -- 0x11
  constant A_HARTINFO   : std_logic_vector(6 downto 0) := "0010010";  -- 0x12
  constant A_ABSTRACTCS : std_logic_vector(6 downto 0) := "0010110";  -- 0x16
  constant A_COMMAND    : std_logic_vector(6 downto 0) := "0010111";  -- 0x17

  signal dmactive_r  : std_logic := '0';
  signal ndmreset_r  : std_logic := '0';
  signal haltreq_r   : std_logic := '0';
  signal havereset_r : std_logic := '0';
  signal cmderr_r    : std_logic_vector(2 downto 0) := "000";

  signal resume_pulse_r : std_logic := '0';

  signal rdata_r : std_logic_vector(31 downto 0) := (others => '0');
  signal ready_r : std_logic := '0';

begin

  process (clk, rst_n)
    variable dmstatus_v : std_logic_vector(31 downto 0);
  begin
    if rst_n = '0' then
      dmactive_r     <= '0';
      ndmreset_r     <= '0';
      haltreq_r      <= '0';
      havereset_r    <= '0';
      cmderr_r       <= "000";
      resume_pulse_r <= '0';
      rdata_r        <= (others => '0');
      ready_r        <= '0';
    elsif rising_edge(clk) then
      ready_r        <= '0';
      resume_pulse_r <= '0';

      if dmi_valid = '1' then
        ready_r <= '1';

        if dmi_op = "10" then  -- write
          if dmi_addr = A_DMCONTROL then
            if dmi_wdata(0) = '0' then
              -- dmactive=0: full DM reset; every other bit ignored.
              dmactive_r  <= '0';
              ndmreset_r  <= '0';
              haltreq_r   <= '0';
              havereset_r <= '0';
              cmderr_r    <= "000";
            else
              dmactive_r <= '1';
              if dmactive_r = '1' then
                -- Other fields honored only once DM already active.
                haltreq_r  <= dmi_wdata(31);
                if dmi_wdata(30) = '1' then
                  resume_pulse_r <= '1';
                end if;
                if dmi_wdata(1) = '1' and ndmreset_r = '0' then
                  havereset_r <= '1';  -- ndmreset 0->1: hart has been reset
                end if;
                ndmreset_r <= dmi_wdata(1);
                if dmi_wdata(28) = '1' then
                  havereset_r <= '0';  -- ackhavereset
                end if;
              end if;
            end if;
          elsif dmi_addr = A_ABSTRACTCS then
            if dmactive_r = '1' then
              cmderr_r <= cmderr_r and not dmi_wdata(10 downto 8);  -- W1C
            end if;
          elsif dmi_addr = A_COMMAND then
            if dmactive_r = '1' and cmderr_r = "000" then
              cmderr_r <= "010";  -- 2 = command not supported (Stage 3 TBD)
            end if;
          end if;
          -- other addresses: write ignored

        elsif dmi_op = "01" then  -- read
          rdata_r <= (others => '0');
          if dmi_addr = A_DMCONTROL then
            if dmactive_r = '1' then
              rdata_r(0) <= '1';
              rdata_r(1) <= ndmreset_r;
            end if;
          elsif dmi_addr = A_DMSTATUS then
            dmstatus_v := (others => '0');
            dmstatus_v(3 downto 0) := "0010";  -- version 2 = spec 0.13
            dmstatus_v(7) := '1';              -- authenticated (no auth unit)
            if dmactive_r = '1' then
              dmstatus_v(8)  := halted_i;      -- anyhalted
              dmstatus_v(9)  := halted_i;      -- allhalted
              dmstatus_v(10) := running_i;     -- anyrunning
              dmstatus_v(11) := running_i;     -- allrunning
              dmstatus_v(16) := resumeack_i;   -- anyresumeack
              dmstatus_v(17) := resumeack_i;   -- allresumeack
              dmstatus_v(18) := havereset_r;   -- anyhavereset
              dmstatus_v(19) := havereset_r;   -- allhavereset
            end if;
            rdata_r <= dmstatus_v;
          elsif dmi_addr = A_ABSTRACTCS then
            rdata_r(10 downto 8) <= cmderr_r;
          end if;
          -- HARTINFO and all other 0x1x registers read as 0
        end if;
      end if;
    end if;
  end process;

  dmi_rdata <= rdata_r;
  dmi_resp  <= "00";  -- all DM-range accesses succeed
  dmi_ready <= ready_r;

  dmactive_o        <= dmactive_r;
  ndmreset_o        <= ndmreset_r;
  haltreq_o         <= haltreq_r;
  resumereq_pulse_o <= resume_pulse_r;

end architecture rtl;
