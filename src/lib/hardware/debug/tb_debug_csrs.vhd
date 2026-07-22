-- tb_debug_csrs.vhd — Stage-4 testbench: debug CSRs (dpc/dcsr) + data-window
-- routing through the real dmi_bus.
--
-- Drives the DM through dmi_bus (Stage-4 routing: scratch 0x00..0x03,
-- abstract-data window 0x04..0x0B and DM regs 0x10..0x1F all on one bus).
-- The fake hart models: haltreq -> halted after 3 cycles (pc frozen, prv=3
-- injected), resumereq -> running after 3 cycles restarting at dpc_o, and
-- single-step (step_o=1 at resume -> run exactly one instruction, pc += 4,
-- then re-halt without haltreq). A fake 32 x 64-bit GPR regfile answers the
-- Stage-3 GPR port for the in-bench regression.
--
-- Checks:
--   CHECK1: haltreq halt -> abstract read dcsr (0x7B0, aarsize=2):
--           xdebugver=4, cause=3, prv=3, step=0
--   CHECK2: abstract read dpc (0x7B1, aarsize=3) == fake hart's halt pc
--   CHECK3: abstract write dpc=0x8000_0040, resume -> hart restarts at
--           0x8000_0040 (resume_pc capture); re-halt -> cause=3 again
--   CHECK4: write dcsr.step=1, resume -> hart runs ONE instruction and
--           re-halts; allresumeack held; dcsr.cause=4
--   CHECK5: unknown CSR regno 0x340 (mscratch) -> cmderr=2; W1C clears
--   CHECK6: all-stage in-bench regressions: Stage-3 GPR abstract write/read
--           x5 through the bus; Stage-2 ndmreset -> havereset ->
--           ackhavereset; Stage-1 scratch 0x00/0x03 round-trip.
--           (Full tb_jtag_dtm_dmi / tb_debug_module / tb_abstract_cmds runs
--           are the external regression gate.)
-- Ends with: report "JTAG STAGE4 PASS"

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use std.env.all;

entity tb_debug_csrs is
end entity tb_debug_csrs;

architecture sim of tb_debug_csrs is

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

  -- Stage-4 debug-CSR hart stub wiring
  signal dpc_s  : std_logic_vector(63 downto 0);
  signal step_s : std_logic;

  signal hart_halted : std_logic := '0';
  signal hart_pc     : std_logic_vector(63 downto 0) := x"0000000080000000";
  signal halt_pc     : std_logic_vector(63 downto 0) := (others => '0');
  signal resume_pc   : std_logic_vector(63 downto 0) := (others => '0');

  -- DM <-> fake hart (Stage-3 GPR port, for the in-bench regression)
  signal gpr_re_s    : std_logic;
  signal gpr_we_s    : std_logic;
  signal gpr_regno_s : std_logic_vector(4 downto 0);
  signal gpr_wdata_s : std_logic_vector(63 downto 0);
  signal gpr_rdata_s : std_logic_vector(63 downto 0) := (others => '0');
  signal gpr_ack_s   : std_logic := '0';

  type regfile_t is array (0 to 31) of std_logic_vector(63 downto 0);
  signal regs : regfile_t := (others => (others => '0'));

  constant A_DATA0      : std_logic_vector(6 downto 0) := "0000100";  -- 0x04
  constant A_DATA1      : std_logic_vector(6 downto 0) := "0000101";  -- 0x05
  constant A_DMCONTROL  : std_logic_vector(6 downto 0) := "0010000";  -- 0x10
  constant A_DMSTATUS   : std_logic_vector(6 downto 0) := "0010001";  -- 0x11
  constant A_ABSTRACTCS : std_logic_vector(6 downto 0) := "0010110";  -- 0x16
  constant A_COMMAND    : std_logic_vector(6 downto 0) := "0010111";  -- 0x17
  constant A_SCRATCH0   : std_logic_vector(6 downto 0) := "0000000";  -- 0x00
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
      halted_i => halted_s, running_i => running_s,
      gpr_re_o => gpr_re_s, gpr_we_o => gpr_we_s,
      gpr_regno_o => gpr_regno_s, gpr_wdata_o => gpr_wdata_s,
      gpr_rdata_i => gpr_rdata_s, gpr_ack_i => gpr_ack_s,
      pc_i => hart_pc, prv_i => "11", ebreak_i => '0',
      dpc_o => dpc_s, step_o => step_s);

  -- Fake hart: free-running pc (+4/cycle). haltreq -> halted after 3 cycles
  -- (pc frozen). resumereq -> running after 3 cycles, restarting at dpc_o;
  -- if step_o=1 at that moment, runs exactly ONE instruction (pc += 4) and
  -- re-halts on its own (no haltreq).
  fake_hart : process (clk, rst_n)
    variable cnt      : natural := 0;
    variable step_cnt : natural := 0;
    variable stepping : boolean := false;
  begin
    if rst_n = '0' then
      hart_halted <= '0';
      hart_pc     <= x"0000000080000000";
      halt_pc     <= (others => '0');
      resume_pc   <= (others => '0');
      cnt := 0; step_cnt := 0; stepping := false;
    elsif rising_edge(clk) then
      if hart_halted = '1' then
        if resumereq_s = '1' then
          if cnt = 3 then
            cnt := 0;
            hart_halted <= '0';
            hart_pc     <= dpc_s;   -- resume at dpc
            resume_pc   <= dpc_s;
            stepping    := (step_s = '1');
            step_cnt    := 0;
          else
            cnt := cnt + 1;
          end if;
        else
          cnt := 0;
        end if;
      else
        if stepping then
          if step_cnt = 1 then      -- ran the one instruction: re-halt
            stepping := false;
            step_cnt := 0;
            hart_halted <= '1';
            halt_pc     <= hart_pc;
          else
            hart_pc  <= std_logic_vector(unsigned(hart_pc) + 4);
            step_cnt := step_cnt + 1;
          end if;
        elsif haltreq_s = '1' then
          if cnt = 3 then
            cnt := 0;
            hart_halted <= '1';
            halt_pc     <= hart_pc;
          else
            cnt := cnt + 1;
            hart_pc <= std_logic_vector(unsigned(hart_pc) + 4);
          end if;
        else
          cnt := 0;
          hart_pc <= std_logic_vector(unsigned(hart_pc) + 4);
        end if;
      end if;
    end if;
  end process fake_hart;

  halted_s  <= hart_halted;
  running_s <= not hart_halted;

  -- Fake 32 x 64-bit GPR regfile: ack after 2 cycles of re/we held high.
  gpr_model : process (clk, rst_n)
    variable cnt : natural := 0;
  begin
    if rst_n = '0' then
      gpr_ack_s   <= '0';
      gpr_rdata_s <= (others => '0');
      cnt := 0;
    elsif rising_edge(clk) then
      gpr_ack_s <= '0';
      if (gpr_re_s = '1' or gpr_we_s = '1') and gpr_ack_s = '0' then
        if cnt = 2 then
          cnt := 0;
          gpr_ack_s <= '1';
          if gpr_we_s = '1' then
            if to_integer(unsigned(gpr_regno_s)) /= 0 then
              regs(to_integer(unsigned(gpr_regno_s))) <= gpr_wdata_s;
            end if;
          else
            gpr_rdata_s <= regs(to_integer(unsigned(gpr_regno_s)));
          end if;
        else
          cnt := cnt + 1;
        end if;
      else
        cnt := 0;
      end if;
    end if;
  end process gpr_model;

  stim : process
    variable rd      : std_logic_vector(31 downto 0);
    variable dpc_lo  : std_logic_vector(31 downto 0);
    variable dpc_hi  : std_logic_vector(31 downto 0);

    -- One DMI transaction through dmi_bus: valid for 1 clock, response
    -- registered 1 clock later; sample mid response cycle.
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

    -- Poll ABSTRACTCS until busy=0; also require cmderr=0.
    procedure wait_cmd_done is
      variable r     : std_logic_vector(31 downto 0);
      variable polls : natural := 0;
    begin
      loop
        dmi_read(A_ABSTRACTCS, r);
        exit when r(12) = '0';
        polls := polls + 1;
        assert polls < 25
          report "abstract command stuck busy, ABSTRACTCS=0x" & to_hstring(r)
          severity failure;
      end loop;
      assert r(10 downto 8) = "000"
        report "abstract command failed, cmderr /= 0, ABSTRACTCS=0x"
               & to_hstring(r) severity failure;
    end procedure wait_cmd_done;

    variable polls : natural;
  begin
    rst_n <= '0';
    wait for 5 * CLK_PERIOD;
    rst_n <= '1';
    wait for 2 * CLK_PERIOD;

    ----------------------------------------------------------------------
    -- Preamble: activate DM, halt the hart via haltreq.
    ----------------------------------------------------------------------
    dmi_write(A_DMCONTROL, x"00000001");  -- dmactive=1
    dmi_write(A_DMCONTROL, x"80000001");  -- haltreq=1, dmactive=1
    polls := 0;
    loop
      dmi_read(A_DMSTATUS, rd);
      exit when rd(9) = '1';              -- allhalted
      polls := polls + 1;
      assert polls < 25
        report "PREAMBLE FAIL: hart did not halt" severity failure;
    end loop;
    dmi_write(A_DMCONTROL, x"00000001");  -- drop haltreq, stay active

    ----------------------------------------------------------------------
    -- CHECK1: read dcsr: xdebugver=4, cause=3 (haltreq), prv=3, step=0.
    ----------------------------------------------------------------------
    dmi_write(A_COMMAND, x"002207B0");    -- read dcsr, aarsize=2
    wait_cmd_done;
    dmi_read(A_DATA0, rd);
    assert rd(31 downto 28) = "0100"
      report "CHECK1 FAIL: dcsr.xdebugver /= 4, dcsr=0x" & to_hstring(rd)
      severity failure;
    assert rd(8 downto 6) = "011"
      report "CHECK1 FAIL: dcsr.cause /= 3 after haltreq halt, dcsr=0x"
             & to_hstring(rd) severity failure;
    assert rd(1 downto 0) = "11"
      report "CHECK1 FAIL: dcsr.prv /= 3 (hart injects prv=3), dcsr=0x"
             & to_hstring(rd) severity failure;
    assert rd(2) = '0'
      report "CHECK1 FAIL: dcsr.step /= 0 after reset, dcsr=0x"
             & to_hstring(rd) severity failure;
    report "CHECK1 PASS: dcsr after haltreq halt: xdebugver=4, cause=3, prv=3"
      severity note;

    ----------------------------------------------------------------------
    -- CHECK2: read dpc (aarsize=3) == fake hart's halt pc.
    ----------------------------------------------------------------------
    dmi_write(A_COMMAND, x"003207B1");    -- read dpc, aarsize=3
    wait_cmd_done;
    dmi_read(A_DATA0, dpc_lo);
    dmi_read(A_DATA1, dpc_hi);
    assert dpc_hi & dpc_lo = halt_pc
      report "CHECK2 FAIL: dpc /= halt pc, dpc=0x" & to_hstring(dpc_hi)
             & to_hstring(dpc_lo) & " halt_pc=0x" & to_hstring(halt_pc)
      severity failure;
    report "CHECK2 PASS: dpc == halt pc (0x" & to_hstring(dpc_hi)
           & to_hstring(dpc_lo) & ")" severity note;

    ----------------------------------------------------------------------
    -- CHECK3: write dpc=0x8000_0040, resume -> hart restarts there.
    ----------------------------------------------------------------------
    dmi_write(A_DATA0, x"80000040");
    dmi_write(A_DATA1, x"00000000");
    dmi_write(A_COMMAND, x"003307B1");    -- write dpc, aarsize=3
    wait_cmd_done;
    dmi_write(A_DMCONTROL, x"40000001");  -- resumereq=1, haltreq=0
    polls := 0;
    loop
      dmi_read(A_DMSTATUS, rd);
      exit when rd(17) = '1' and rd(11) = '1';  -- allresumeack + allrunning
      polls := polls + 1;
      assert polls < 25
        report "CHECK3 FAIL: hart did not resume" severity failure;
    end loop;
    assert resume_pc = x"0000000080000040"
      report "CHECK3 FAIL: hart did not restart at written dpc, resume_pc=0x"
             & to_hstring(resume_pc) severity failure;
    -- Re-halt for the following checks; cause must be 3 again (haltreq).
    dmi_write(A_DMCONTROL, x"80000001");
    polls := 0;
    loop
      dmi_read(A_DMSTATUS, rd);
      exit when rd(9) = '1';
      polls := polls + 1;
      assert polls < 25
        report "CHECK3 FAIL: hart did not re-halt" severity failure;
    end loop;
    dmi_write(A_DMCONTROL, x"00000001");  -- drop haltreq
    dmi_write(A_COMMAND, x"002207B0");    -- read dcsr
    wait_cmd_done;
    dmi_read(A_DATA0, rd);
    assert rd(8 downto 6) = "011"
      report "CHECK3 FAIL: cause /= 3 after haltreq re-halt, dcsr=0x"
             & to_hstring(rd) severity failure;
    report "CHECK3 PASS: resume-at-dpc (0x80000040) + haltreq re-halt cause=3"
      severity note;

    ----------------------------------------------------------------------
    -- CHECK4: dcsr.step=1, resume -> one instruction -> re-halt, cause=4.
    ----------------------------------------------------------------------
    dmi_write(A_DATA0, x"00000007");      -- step=1, prv=3
    dmi_write(A_COMMAND, x"002307B0");    -- write dcsr, aarsize=2
    wait_cmd_done;
    dmi_write(A_COMMAND, x"002207B0");    -- read back dcsr
    wait_cmd_done;
    dmi_read(A_DATA0, rd);
    assert rd(2) = '1'
      report "CHECK4 FAIL: dcsr.step did not set, dcsr=0x" & to_hstring(rd)
      severity failure;
    -- Pin dpc to a known value (the re-halt in CHECK3 re-captured it at an
    -- arbitrary free-running pc) so the one-instruction step is checkable.
    dmi_write(A_DATA0, x"80000040");
    dmi_write(A_DATA1, x"00000000");
    dmi_write(A_COMMAND, x"003307B1");    -- write dpc, aarsize=3
    wait_cmd_done;
    dmi_write(A_DMCONTROL, x"40000001");  -- resumereq=1, haltreq=0
    -- Poll the LATCHED allresumeack first (the running window of a single
    -- step is only ~2 cycles — polling allhalted right away would sample
    -- the stale pre-resume halted state and race the handshake).
    polls := 0;
    loop
      dmi_read(A_DMSTATUS, rd);
      exit when rd(17) = '1';             -- allresumeack (sticky until next resumereq)
      polls := polls + 1;
      assert polls < 25
        report "CHECK4 FAIL: allresumeack not set across the step, DMSTATUS=0x"
               & to_hstring(rd) severity failure;
    end loop;
    polls := 0;
    loop
      dmi_read(A_DMSTATUS, rd);
      exit when rd(9) = '1';              -- re-halted after the single step
      polls := polls + 1;
      assert polls < 25
        report "CHECK4 FAIL: hart did not re-halt after single step"
        severity failure;
    end loop;
    dmi_write(A_COMMAND, x"002207B0");    -- read dcsr
    wait_cmd_done;
    dmi_read(A_DATA0, rd);
    assert rd(8 downto 6) = "100"
      report "CHECK4 FAIL: dcsr.cause /= 4 after single step, dcsr=0x"
             & to_hstring(rd) severity failure;
    assert halt_pc = x"0000000080000044"
      report "CHECK4 FAIL: step did not execute exactly one instruction, "
             & "halt_pc=0x" & to_hstring(halt_pc) severity failure;
    dmi_write(A_COMMAND, x"003207B1");    -- read dpc: re-captured at re-halt
    wait_cmd_done;
    dmi_read(A_DATA0, dpc_lo);
    dmi_read(A_DATA1, dpc_hi);
    assert dpc_hi & dpc_lo = x"0000000080000044"
      report "CHECK4 FAIL: dpc not re-captured at step re-halt, dpc=0x"
             & to_hstring(dpc_hi) & to_hstring(dpc_lo) severity failure;
    -- Clear step for the remaining checks.
    dmi_write(A_DATA0, x"00000003");      -- step=0, prv=3
    dmi_write(A_COMMAND, x"002307B0");
    wait_cmd_done;
    report "CHECK4 PASS: step=1 resume -> one instruction -> re-halt cause=4, "
           & "allresumeack held" severity note;

    ----------------------------------------------------------------------
    -- CHECK5: unknown CSR regno 0x340 (mscratch; 0x300 mstatus is a Stage-5 DM stub now) -> cmderr=2; W1C clears.
    ----------------------------------------------------------------------
    dmi_write(A_COMMAND, x"00230340");    -- write mscratch: unsupported
    dmi_read(A_ABSTRACTCS, rd);
    assert rd(10 downto 8) = "010"
      report "CHECK5 FAIL: cmderr /= 2 for CSR 0x340, ABSTRACTCS=0x"
             & to_hstring(rd) severity failure;
    dmi_write(A_ABSTRACTCS, x"00000700"); -- W1C
    dmi_read(A_ABSTRACTCS, rd);
    assert rd(10 downto 8) = "000"
      report "CHECK5 FAIL: cmderr not cleared by W1C, ABSTRACTCS=0x"
             & to_hstring(rd) severity failure;
    report "CHECK5 PASS: unknown CSR regno 0x340 -> cmderr=2; W1C clears"
      severity note;

    ----------------------------------------------------------------------
    -- CHECK6: all-stage in-bench regressions.
    ----------------------------------------------------------------------
    -- Stage 3: GPR abstract write/read x5 through the bus.
    dmi_write(A_DATA0, x"CAFED00D");
    dmi_write(A_COMMAND, x"00231005");    -- write x5, aarsize=2
    wait_cmd_done;
    wait for CLK_PERIOD;
    assert regs(5) = x"00000000CAFED00D"
      report "CHECK6 FAIL: x5 /= 0xCAFED00D via bus, got 0x"
             & to_hstring(regs(5)) severity failure;
    dmi_write(A_DATA0, x"00000000");
    dmi_write(A_COMMAND, x"00221005");    -- read x5, aarsize=2
    wait_cmd_done;
    dmi_read(A_DATA0, rd);
    assert rd = x"CAFED00D"
      report "CHECK6 FAIL: DATA0 /= 0xCAFED00D after read x5, got 0x"
             & to_hstring(rd) severity failure;
    -- Stage 2: ndmreset -> havereset; ackhavereset clears.
    dmi_write(A_DMCONTROL, x"00000003");  -- ndmreset=1
    dmi_write(A_DMCONTROL, x"00000001");  -- ndmreset=0
    dmi_read(A_DMSTATUS, rd);
    assert rd(18) = '1' and rd(19) = '1'
      report "CHECK6 FAIL: havereset not set after ndmreset, DMSTATUS=0x"
             & to_hstring(rd) severity failure;
    dmi_write(A_DMCONTROL, x"10000001");  -- ackhavereset
    dmi_read(A_DMSTATUS, rd);
    assert rd(18) = '0' and rd(19) = '0'
      report "CHECK6 FAIL: havereset not cleared, DMSTATUS=0x" & to_hstring(rd)
      severity failure;
    -- Stage 1: scratch round-trip on the same bus.
    dmi_write(A_SCRATCH3, x"DEADBEEF");
    dmi_read(A_SCRATCH3, rd);
    assert rd = x"DEADBEEF"
      report "CHECK6 FAIL: scratch 0x03 round-trip broke, got 0x"
             & to_hstring(rd) severity failure;
    dmi_write(A_SCRATCH0, x"A5A5A5A5");
    dmi_read(A_SCRATCH0, rd);
    assert rd = x"A5A5A5A5"
      report "CHECK6 FAIL: scratch 0x00 round-trip broke, got 0x"
             & to_hstring(rd) severity failure;
    report "CHECK6 PASS: Stage-1/2/3 in-bench regressions intact"
      severity note;

    report "JTAG STAGE4 PASS" severity note;
    finish;
  end process stim;

end architecture sim;
