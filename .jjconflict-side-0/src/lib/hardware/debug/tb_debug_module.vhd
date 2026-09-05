-- tb_debug_module.vhd — Stage-2 testbench: Debug Module over the DMI bus.
--
-- Drives the dmi_bus master port directly (JTAG/DTM path is exercised by the
-- Stage-1 testbench, which stays green — CHECK6 covers the shared scratch
-- range regression here). A fake hart model answers haltreq/resumereq with a
-- few cycles of latency.
--
-- Checks:
--   CHECK1: dmactive=0 -> DMCONTROL reads back 0 (other write bits ignored)
--   CHECK2: dmactive=1, haltreq=1 -> DMSTATUS.allhalted within 100 cycles
--   CHECK3: resumereq=1 -> allresumeack=1 and allrunning=1
--   CHECK4: ndmreset pulse -> anyhavereset=1; ackhavereset -> cleared
--   CHECK5: COMMAND write while hart running -> ABSTRACTCS.cmderr=4
--           (haltresume, Stage-3 semantics) sticky; W1C clears
--   CHECK6: scratch regfile 0x03 round-trip still works (Stage-1 regression
--           in-bench; full Stage-1 tb run is the external regression gate)
-- Ends with: report "JTAG STAGE2 PASS"

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use std.env.all;

entity tb_debug_module is
end entity tb_debug_module;

architecture sim of tb_debug_module is

  constant CLK_PERIOD : time := 10 ns;

  signal clk   : std_logic := '0';
  signal rst_n : std_logic := '0';

  -- DMI master -> dmi_bus
  signal dmi_valid : std_logic := '0';
  signal dmi_addr  : std_logic_vector(6 downto 0) := (others => '0');
  signal dmi_wdata : std_logic_vector(31 downto 0) := (others => '0');
  signal dmi_op    : std_logic_vector(1 downto 0) := "00";
  signal dmi_rdata : std_logic_vector(31 downto 0);
  signal dmi_resp  : std_logic_vector(1 downto 0);
  signal dmi_ready : std_logic;

  -- dmi_bus <-> debug module
  signal dm_valid : std_logic;
  signal dm_addr  : std_logic_vector(6 downto 0);
  signal dm_wdata : std_logic_vector(31 downto 0);
  signal dm_op    : std_logic_vector(1 downto 0);
  signal dm_rdata : std_logic_vector(31 downto 0);
  signal dm_resp  : std_logic_vector(1 downto 0);
  signal dm_ready : std_logic;

  -- DM <-> fake hart
  signal haltreq_s   : std_logic;
  signal resumereq_s : std_logic;
  signal ndmreset_s  : std_logic;
  signal halted_s    : std_logic;
  signal running_s   : std_logic;

  signal hart_halted : std_logic := '0';

  constant A_DMCONTROL  : std_logic_vector(6 downto 0) := "0010000";  -- 0x10
  constant A_DMSTATUS   : std_logic_vector(6 downto 0) := "0010001";  -- 0x11
  constant A_ABSTRACTCS : std_logic_vector(6 downto 0) := "0010110";  -- 0x16
  constant A_COMMAND    : std_logic_vector(6 downto 0) := "0010111";  -- 0x17
  constant A_SCRATCH3   : std_logic_vector(6 downto 0) := "0000011";  -- 0x03

begin

  clk <= not clk after CLK_PERIOD / 2;

  u_dmi : entity work.dmi_bus
    port map (
      clk => clk, rst_n => rst_n,
      valid => dmi_valid, addr => dmi_addr, wdata => dmi_wdata, op => dmi_op,
      rdata => dmi_rdata, resp => dmi_resp, ready => dmi_ready,
      dm_valid => dm_valid, dm_addr => dm_addr,
      dm_wdata => dm_wdata, dm_op => dm_op,
      dm_rdata => dm_rdata, dm_resp => dm_resp, dm_ready => dm_ready);

  u_dm : entity work.riscv_debug_module
    port map (
      clk => clk, rst_n => rst_n,
      dmi_valid => dm_valid, dmi_addr => dm_addr,
      dmi_wdata => dm_wdata, dmi_op => dm_op,
      dmi_rdata => dm_rdata, dmi_resp => dm_resp, dmi_ready => dm_ready,
      haltreq_o => haltreq_s, resumereq_o => resumereq_s,
      ndmreset_o => ndmreset_s,
      halted_i => halted_s, running_i => running_s);

  -- Fake hart: haltreq -> halted after 3 cycles; resumereq -> running after 3.
  fake_hart : process (clk, rst_n)
    variable cnt : natural := 0;
  begin
    if rst_n = '0' then
      hart_halted <= '0';
      cnt := 0;
    elsif rising_edge(clk) then
      if hart_halted = '0' and haltreq_s = '1' then
        if cnt = 3 then
          hart_halted <= '1';
          cnt := 0;
        else
          cnt := cnt + 1;
        end if;
      elsif hart_halted = '1' and resumereq_s = '1' then
        if cnt = 3 then
          hart_halted <= '0';
          cnt := 0;
        else
          cnt := cnt + 1;
        end if;
      else
        cnt := 0;
      end if;
    end if;
  end process fake_hart;

  halted_s  <= hart_halted;
  running_s <= not hart_halted;

  stim : process
    variable rd : std_logic_vector(31 downto 0);

    -- One DMI transaction: valid for 1 clock, response registered 1 clock
    -- later; sample outputs the clock after that (they hold until the next
    -- request).
    procedure dmi_xact(a : std_logic_vector(6 downto 0);
                       d : std_logic_vector(31 downto 0);
                       o : std_logic_vector(1 downto 0);
                       variable data : out std_logic_vector(31 downto 0)) is
    begin
      wait until rising_edge(clk);
      dmi_addr  <= a;
      dmi_wdata <= d;
      dmi_op    <= o;
      dmi_valid <= '1';
      wait until rising_edge(clk);   -- request sampled here
      dmi_valid <= '0';
      wait for CLK_PERIOD / 2;       -- mid response cycle: ready must pulse
      assert dmi_ready = '1'
        report "DMI transaction did not complete (no ready)" severity failure;
      assert dmi_resp = "00"
        report "DMI resp /= success" severity failure;
      data := dmi_rdata;
      wait until rising_edge(clk);   -- resync
    end procedure dmi_xact;

    procedure dmi_write(a : std_logic_vector(6 downto 0);
                        d : std_logic_vector(31 downto 0)) is
      variable dummy : std_logic_vector(31 downto 0);
    begin
      dmi_xact(a, d, "10", dummy);
    end procedure dmi_write;

    procedure dmi_read(a : std_logic_vector(6 downto 0);
                       variable data : out std_logic_vector(31 downto 0)) is
    begin
      dmi_xact(a, x"00000000", "01", data);
    end procedure dmi_read;

    variable polls : natural;
  begin
    rst_n <= '0';
    wait for 5 * CLK_PERIOD;
    rst_n <= '1';
    wait for 2 * CLK_PERIOD;

    ----------------------------------------------------------------------
    -- CHECK1: dmactive=0 — write haltreq|ndmreset with dmactive=0, then
    -- read DMCONTROL back: must be all zero.
    ----------------------------------------------------------------------
    dmi_write(A_DMCONTROL, x"80000002");  -- haltreq=1, ndmreset=1, dmactive=0
    dmi_read(A_DMCONTROL, rd);
    assert rd = x"00000000"
      report "CHECK1 FAIL: DMCONTROL /= 0 while dmactive=0, got 0x"
             & to_hstring(rd) severity failure;
    report "CHECK1 PASS: dmactive=0 -> DMCONTROL reads 0, writes ignored"
      severity note;

    ----------------------------------------------------------------------
    -- CHECK2: activate DM, request halt, poll DMSTATUS.allhalted.
    ----------------------------------------------------------------------
    dmi_write(A_DMCONTROL, x"00000001");  -- dmactive=1
    dmi_read(A_DMCONTROL, rd);
    assert rd(0) = '1'
      report "CHECK2 FAIL: dmactive did not read back 1" severity failure;
    dmi_read(A_DMSTATUS, rd);
    assert rd(3 downto 0) = "0010"
      report "CHECK2 FAIL: DMSTATUS.version /= 2, got 0x" & to_hstring(rd)
      severity failure;
    assert rd(11) = '1' and rd(9) = '0'
      report "CHECK2 FAIL: hart not initially running, DMSTATUS=0x"
             & to_hstring(rd) severity failure;

    dmi_write(A_DMCONTROL, x"80000001");  -- haltreq=1, dmactive=1
    polls := 0;
    loop
      dmi_read(A_DMSTATUS, rd);
      exit when rd(9) = '1';              -- allhalted
      polls := polls + 1;
      assert polls < 25                   -- 25 polls * 4 clks << 100 cycles
        report "CHECK2 FAIL: allhalted not set within 100 cycles"
        severity failure;
    end loop;
    assert rd(8) = '1' and rd(11) = '0' and rd(10) = '0'
      report "CHECK2 FAIL: inconsistent halted/running, DMSTATUS=0x"
             & to_hstring(rd) severity failure;
    report "CHECK2 PASS: haltreq -> allhalted (DMSTATUS=0x" & to_hstring(rd)
           & ")" severity note;

    ----------------------------------------------------------------------
    -- CHECK3: resume — haltreq=0, resumereq=1; expect allresumeack and
    -- allrunning.
    ----------------------------------------------------------------------
    dmi_write(A_DMCONTROL, x"40000001");  -- resumereq=1, haltreq=0, dmactive=1
    polls := 0;
    loop
      dmi_read(A_DMSTATUS, rd);
      exit when rd(17) = '1';             -- allresumeack
      polls := polls + 1;
      assert polls < 25
        report "CHECK3 FAIL: allresumeack not set" severity failure;
    end loop;
    assert rd(16) = '1' and rd(11) = '1' and rd(10) = '1' and rd(9) = '0'
      report "CHECK3 FAIL: expected running+resumeack, DMSTATUS=0x"
             & to_hstring(rd) severity failure;
    report "CHECK3 PASS: resumereq -> allresumeack=1, allrunning=1"
      severity note;

    ----------------------------------------------------------------------
    -- CHECK4: ndmreset pulse sets havereset; ackhavereset clears it.
    ----------------------------------------------------------------------
    dmi_write(A_DMCONTROL, x"00000003");  -- ndmreset=1, dmactive=1
    dmi_write(A_DMCONTROL, x"00000001");  -- ndmreset=0
    dmi_read(A_DMSTATUS, rd);
    assert rd(18) = '1' and rd(19) = '1'
      report "CHECK4 FAIL: anyhavereset not set after ndmreset pulse, "
             & "DMSTATUS=0x" & to_hstring(rd) severity failure;
    dmi_write(A_DMCONTROL, x"10000001");  -- ackhavereset=1, dmactive=1
    dmi_read(A_DMSTATUS, rd);
    assert rd(18) = '0' and rd(19) = '0'
      report "CHECK4 FAIL: havereset not cleared by ackhavereset, "
             & "DMSTATUS=0x" & to_hstring(rd) severity failure;
    report "CHECK4 PASS: ndmreset -> havereset; ackhavereset clears"
      severity note;

    ----------------------------------------------------------------------
    -- CHECK5: COMMAND while hart running -> cmderr=4 (haltresume),
    -- sticky, W1C. (Stage 3: the command itself is now a supported
    -- access-register command; the Stage-2 provisional cmderr=2 was
    -- explicitly "Stage 3 TBD".)
    ----------------------------------------------------------------------
    dmi_read(A_ABSTRACTCS, rd);
    assert rd = x"00000002"               -- datacount=2, busy=0, cmderr=0
      report "CHECK5 FAIL: ABSTRACTCS /= datacount-only before COMMAND "
             & "write, got 0x" & to_hstring(rd) severity failure;
    dmi_write(A_COMMAND, x"00231000");    -- valid access-register command
    dmi_read(A_ABSTRACTCS, rd);
    assert rd(10 downto 8) = "100"
      report "CHECK5 FAIL: cmderr /= 4 for COMMAND while running, "
             & "ABSTRACTCS=0x" & to_hstring(rd) severity failure;
    dmi_write(A_COMMAND, x"00331000");    -- second write: cmderr stays 4
    dmi_read(A_ABSTRACTCS, rd);
    assert rd(10 downto 8) = "100"
      report "CHECK5 FAIL: cmderr not sticky, ABSTRACTCS=0x" & to_hstring(rd)
      severity failure;
    dmi_write(A_ABSTRACTCS, x"00000700"); -- write 1s to cmderr -> clear
    dmi_read(A_ABSTRACTCS, rd);
    assert rd(10 downto 8) = "000"
      report "CHECK5 FAIL: cmderr not cleared by W1C, ABSTRACTCS=0x"
             & to_hstring(rd) severity failure;
    report "CHECK5 PASS: COMMAND while running -> cmderr=4 sticky, W1C clears"
      severity note;

    ----------------------------------------------------------------------
    -- CHECK6: Stage-1 scratch regfile (0x00..0x07) still routed correctly.
    ----------------------------------------------------------------------
    dmi_write(A_SCRATCH3, x"DEADBEEF");
    dmi_read(A_SCRATCH3, rd);
    assert rd = x"DEADBEEF"
      report "CHECK6 FAIL: scratch 0x03 round-trip broke, got 0x"
             & to_hstring(rd) severity failure;
    report "CHECK6 PASS: scratch regfile round-trip intact after DM routing"
      severity note;

    report "JTAG STAGE2 PASS" severity note;
    finish;
  end process stim;

end architecture sim;
