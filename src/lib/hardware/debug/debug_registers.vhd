-- debug_registers.vhd — RISC-V Debug Spec v0.13 DM register block (Stage 3).
--
-- DMI slave for addresses 0x10..0x1F plus the abstract-data registers
-- 0x04/0x05 (same 1-cycle valid/ready protocol as dmi_bus scratch): request
-- sampled on the clock where dmi_valid = '1', response (rdata/resp/ready)
-- driven the following clock, ready for 1 clock.
--
-- Implemented registers:
--   0x04 DATA0     — abstract command data, low word (r/w).
--   0x05 DATA1     — abstract command data, high word (r/w).
--                    NOTE: in the full JTAG chain dmi_bus currently keeps
--                    0x00..0x07 as its Stage-1 scratch regfile and forwards
--                    only 0x10..0x1F here. Forwarding 0x04..0x05 (data0/1)
--                    to the DM is a Stage-4 integration prerequisite —
--                    dmi_bus is frozen in this stage. The DM decodes them
--                    for direct-DMI integrations and the Stage-3 testbench.
--   0x10 DMCONTROL  — dmactive(0), ndmreset(1), ackhavereset(28, W1),
--                     resumereq(30, W1 pulse), haltreq(31, level).
--                     Single hart: hasel/hartsello/hartselhi ignored, read 0.
--                     haltreq/resumereq/ackhavereset are write-only (read 0)
--                     per spec field access "W".
--   0x11 DMSTATUS   — version=2 (0.13), authenticated=1 (no auth), and
--                     single-hart status: all==any for halted/running/
--                     resumeack/havereset.
--   0x12 HARTINFO   — all zero (nscratch=0, dataaccess=0, datasize=0).
--   0x16 ABSTRACTCS — datacount(3:0)=2, busy(12), cmderr(10:8, W1C);
--                     progbufsize(28:24)=0 (no program buffer).
--   0x17 COMMAND    — cmdtype 0 (access register) only:
--                       aarsize(22:20): 2 = 32-bit, 3 = 64-bit;
--                       transfer(17), write(16), regno(15:0).
--                     Supported regno: 0x1000..0x101F (GPRs x0..x31).
--                     cmderr encoding (sticky; new COMMAND writes while
--                     cmderr /= 0 are ignored; W1C via ABSTRACTCS):
--                       1 = busy violation: COMMAND/DATA0/DATA1 written
--                           while an abstract command is executing;
--                       2 = not supported: cmdtype /= 0, aarsize not 2/3,
--                           or transfer=1 with regno outside 0x1000..0x101F;
--                       4 = haltresume: command issued while the hart is not
--                           halted (halted_i = '0').
--                     Check order: busy (1) -> not-supported (2) ->
--                     not-halted (4). transfer=0 with an otherwise valid
--                     command is a successful no-op (still requires halted).
--                     aarsize=2 write zero-extends DATA0 into the 64-bit
--                     GPR; aarsize=2 read returns the low 32 bits in DATA0
--                     and leaves DATA1 unchanged. Writes to regno 0x1000
--                     (x0) are accepted by the DM; the hart keeps x0 = 0.
--                     Reads of DATA0/1 while busy return the current values
--                     without setting cmderr (spec allows cmderr=1 here;
--                     scoped to writes in this implementation).
--   other 0x1x      — read 0 / write ignored, resp = success (harmless
--                     unimplemented optional registers: haltsum, hawindow...).
--
-- Abstract command execution (GPR port): on an accepted transfer command the
-- block asserts gpr_re_o or gpr_we_o (level) with gpr_regno_o/gpr_wdata_o
-- held stable until the hart pulses gpr_ack_i for one clock; busy is set for
-- the whole window. On read-ack, gpr_rdata_i is captured into DATA0 (and
-- DATA1 when aarsize=3).
--
-- dmactive semantics: writing DMCONTROL with dmactive=0 resets ALL DM state
-- (including DATA0/1, busy, cmderr and any in-flight GPR access). While
-- dmactive=0, DMCONTROL reads back 0 and all other write bits of the
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

    -- DMI slave (forwarded 0x10..0x1F requests from dmi_bus; 0x04/0x05 for
    -- direct-DMI integrations — see header note)
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

    -- Abstract-command GPR port toward the hart (Stage 3; stub-level,
    -- matches the deferred hart integration): re/we held with regno/wdata
    -- until ack_i pulses for one clock.
    gpr_re_o    : out std_logic;
    gpr_we_o    : out std_logic;
    gpr_regno_o : out std_logic_vector(4 downto 0);
    gpr_wdata_o : out std_logic_vector(63 downto 0);
    gpr_rdata_i : in  std_logic_vector(63 downto 0) := (others => '0');
    gpr_ack_i   : in  std_logic := '0';

    -- Status inputs (from DM core / hart)
    halted_i    : in  std_logic;
    running_i   : in  std_logic;
    resumeack_i : in  std_logic
  );
end entity debug_registers;

architecture rtl of debug_registers is

  constant A_DATA0      : std_logic_vector(6 downto 0) := "0000100";  -- 0x04
  constant A_DATA1      : std_logic_vector(6 downto 0) := "0000101";  -- 0x05
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

  -- Abstract command state (Stage 3)
  signal data0_r       : std_logic_vector(31 downto 0) := (others => '0');
  signal data1_r       : std_logic_vector(31 downto 0) := (others => '0');
  signal abusy_r       : std_logic := '0';
  signal exec_write_r  : std_logic := '0';
  signal exec_size64_r : std_logic := '0';
  signal gpr_re_r      : std_logic := '0';
  signal gpr_we_r      : std_logic := '0';
  signal gpr_regno_r   : std_logic_vector(4 downto 0) := (others => '0');
  signal gpr_wdata_r   : std_logic_vector(63 downto 0) := (others => '0');

  signal rdata_r : std_logic_vector(31 downto 0) := (others => '0');
  signal ready_r : std_logic := '0';

begin

  process (clk, rst_n)
    variable dmstatus_v : std_logic_vector(31 downto 0);
    variable cmd_supported_v : boolean;
  begin
    if rst_n = '0' then
      dmactive_r     <= '0';
      ndmreset_r     <= '0';
      haltreq_r      <= '0';
      havereset_r    <= '0';
      cmderr_r       <= "000";
      resume_pulse_r <= '0';
      data0_r        <= (others => '0');
      data1_r        <= (others => '0');
      abusy_r        <= '0';
      exec_write_r   <= '0';
      exec_size64_r  <= '0';
      gpr_re_r       <= '0';
      gpr_we_r       <= '0';
      gpr_regno_r    <= (others => '0');
      gpr_wdata_r    <= (others => '0');
      rdata_r        <= (others => '0');
      ready_r        <= '0';
    elsif rising_edge(clk) then
      ready_r        <= '0';
      resume_pulse_r <= '0';

      -- Abstract command completion: hart acknowledged the GPR access.
      if abusy_r = '1' and gpr_ack_i = '1' then
        gpr_re_r <= '0';
        gpr_we_r <= '0';
        abusy_r  <= '0';
        if exec_write_r = '0' then
          data0_r <= gpr_rdata_i(31 downto 0);
          if exec_size64_r = '1' then
            data1_r <= gpr_rdata_i(63 downto 32);
          end if;
        end if;
      end if;

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
              data0_r     <= (others => '0');
              data1_r     <= (others => '0');
              abusy_r     <= '0';
              gpr_re_r    <= '0';
              gpr_we_r    <= '0';
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
          elsif dmi_addr = A_DATA0 then
            if dmactive_r = '1' then
              if abusy_r = '1' then
                if cmderr_r = "000" then
                  cmderr_r <= "001";  -- busy violation; write dropped
                end if;
              else
                data0_r <= dmi_wdata;
              end if;
            end if;
          elsif dmi_addr = A_DATA1 then
            if dmactive_r = '1' then
              if abusy_r = '1' then
                if cmderr_r = "000" then
                  cmderr_r <= "001";  -- busy violation; write dropped
                end if;
              else
                data1_r <= dmi_wdata;
              end if;
            end if;
          elsif dmi_addr = A_ABSTRACTCS then
            if dmactive_r = '1' then
              cmderr_r <= cmderr_r and not dmi_wdata(10 downto 8);  -- W1C
            end if;
          elsif dmi_addr = A_COMMAND then
            if dmactive_r = '1' then
              if abusy_r = '1' then
                if cmderr_r = "000" then
                  cmderr_r <= "001";  -- busy violation
                end if;
              elsif cmderr_r /= "000" then
                null;  -- sticky: command ignored until cmderr cleared (W1C)
              else
                -- Decode access-register command.
                cmd_supported_v :=
                  dmi_wdata(31 downto 24) = x"00"                -- cmdtype 0
                  and (dmi_wdata(22 downto 20) = "010"           -- aarsize 2
                       or dmi_wdata(22 downto 20) = "011")       -- aarsize 3
                  and (dmi_wdata(17) = '0'                       -- no transfer
                       or dmi_wdata(15 downto 5) = "00010000000"); -- 0x1000..0x101F
                if not cmd_supported_v then
                  cmderr_r <= "010";  -- 2 = not supported
                elsif halted_i = '0' then
                  cmderr_r <= "100";  -- 4 = hart not halted
                elsif dmi_wdata(17) = '1' then
                  -- Launch GPR access (transfer=0 is a successful no-op).
                  abusy_r       <= '1';
                  exec_size64_r <= dmi_wdata(20);  -- '0'=32-bit, '1'=64-bit
                  gpr_regno_r   <= dmi_wdata(4 downto 0);
                  if dmi_wdata(16) = '1' then
                    exec_write_r <= '1';
                    gpr_we_r     <= '1';
                    if dmi_wdata(20) = '1' then
                      gpr_wdata_r <= data1_r & data0_r;
                    else
                      gpr_wdata_r <= x"00000000" & data0_r;  -- zero-extend
                    end if;
                  else
                    exec_write_r <= '0';
                    gpr_re_r     <= '1';
                  end if;
                end if;
              end if;
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
          elsif dmi_addr = A_DATA0 then
            rdata_r <= data0_r;
          elsif dmi_addr = A_DATA1 then
            rdata_r <= data1_r;
          elsif dmi_addr = A_ABSTRACTCS then
            rdata_r(3 downto 0)   <= "0010";  -- datacount = 2
            rdata_r(12)           <= abusy_r;
            rdata_r(10 downto 8)  <= cmderr_r;
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

  gpr_re_o    <= gpr_re_r;
  gpr_we_o    <= gpr_we_r;
  gpr_regno_o <= gpr_regno_r;
  gpr_wdata_o <= gpr_wdata_r;

end architecture rtl;
