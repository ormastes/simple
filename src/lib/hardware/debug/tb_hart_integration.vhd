-- tb_hart_integration.vhd — Lane EE: JTAG Debug Module driving the REAL rv32
-- hart through hart_core_glue.  Replaces the Stage-1..5 fake-hart model with
-- the genuine rv32_exec_core (clock-gated for halt).  Drives the DM through the
-- real dmi_bus exactly like the landed Stage tbs.
--
-- Program (rv32_payload.mem, provided by run_hart_e2e.shs in the run dir):
--   0x00: addi x10, x0, 42   (0x02A00513)  -> a0 = 42 (real computed value)
--   0x04: addi x1,  x0, 7    (0x00700093)  -> ra = 7
--   0x08.. : ROM default-fill 0x00000013 = NOP sled (pc marches +4 each retire)
--
-- Stages:
--   A  SBA system-bus write+readback through the glue (DM SB master exercised
--      against a wrapper-owned mem; the core fetches its OWN internal ROM, so
--      this is NOT the core's instruction source — see file header of the glue)
--   B  single-step FROM RESET over addi x10 -> pc += 4 AND x10 (a0) 0 -> 42
--      (proves a step both advances pc AND updates a real x-register)
--   C  resume -> real hart free-runs -> haltreq halts it (clock-gated)
--   D  abstract-command GPR readback: x10 == 42, x1 == 7 (REAL values)
--   E  single-step in the NOP sled: dcsr.step=1, resume -> exactly one
--      instruction retires, dpc advances by exactly 4
--
-- Prints `HART-INT <STAGE> PASS` markers and `JTAG HART E2E: ALL PASS`.

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use std.textio.all;
use std.env.all;

entity tb_hart_integration is
end entity tb_hart_integration;

architecture sim of tb_hart_integration is
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

  -- dmi_bus <-> glue (DM slave side)
  signal dm_valid : std_logic;
  signal dm_addr  : std_logic_vector(6 downto 0);
  signal dm_wdata : std_logic_vector(31 downto 0);
  signal dm_op    : std_logic_vector(1 downto 0);
  signal dm_rdata : std_logic_vector(31 downto 0);
  signal dm_resp  : std_logic_vector(1 downto 0);
  signal dm_ready : std_logic;

  -- glue observation
  signal o_halted   : std_logic;
  signal o_running  : std_logic;
  signal o_step     : std_logic;
  signal o_core_run : std_logic;
  signal o_dbg_pc   : std_logic_vector(15 downto 0);
  signal o_dbg_a0   : std_logic_vector(7 downto 0);
  signal o_dbg_ra   : std_logic_vector(15 downto 0);
  signal o_dbg_sp   : std_logic_vector(15 downto 0);

  -- DMI register addresses (RISC-V debug v0.13)
  constant A_DATA0      : std_logic_vector(6 downto 0) := "0000100";  -- 0x04
  constant A_DATA1      : std_logic_vector(6 downto 0) := "0000101";  -- 0x05
  constant A_DMCONTROL  : std_logic_vector(6 downto 0) := "0010000";  -- 0x10
  constant A_DMSTATUS   : std_logic_vector(6 downto 0) := "0010001";  -- 0x11
  constant A_ABSTRACTCS : std_logic_vector(6 downto 0) := "0010110";  -- 0x16
  constant A_COMMAND    : std_logic_vector(6 downto 0) := "0010111";  -- 0x17
  constant A_SBCS       : std_logic_vector(6 downto 0) := "0111000";  -- 0x38
  constant A_SBADDRESS0 : std_logic_vector(6 downto 0) := "0111001";  -- 0x39
  constant A_SBDATA0    : std_logic_vector(6 downto 0) := "0111100";  -- 0x3C
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

  u_glue : entity work.hart_core_glue
    port map (
      clk => clk, rst_n => rst_n,
      dmi_valid => dm_valid, dmi_addr => dm_addr,
      dmi_wdata => dm_wdata, dmi_op => dm_op,
      dmi_rdata => dm_rdata, dmi_resp => dm_resp, dmi_ready => dm_ready,
      o_halted => o_halted, o_running => o_running, o_step => o_step,
      o_core_run => o_core_run, o_debug_pc => o_dbg_pc,
      o_debug_a0 => o_dbg_a0, o_debug_ra => o_dbg_ra, o_debug_sp => o_dbg_sp);

  stim : process
    variable rd, dpc_lo, dpc_hi : std_logic_vector(31 downto 0);
    variable pc_before, pc_after : unsigned(31 downto 0);
    variable l : line;

    procedure dmi_xact(a : std_logic_vector(6 downto 0);
                       d : std_logic_vector(31 downto 0);
                       o : std_logic_vector(1 downto 0);
                       data : out std_logic_vector(31 downto 0)) is
    begin
      wait until rising_edge(clk);
      dmi_addr <= a; dmi_wdata <= d; dmi_op <= o; dmi_valid <= '1';
      wait until rising_edge(clk);   -- request sampled here (single-cycle valid)
      dmi_valid <= '0';
      wait for CLK_PERIOD / 2;        -- mid response cycle: ready must pulse
      assert dmi_ready = '1'
        report "DMI transaction did not complete (no ready) on 0x" & to_hstring(a)
        severity failure;
      assert dmi_resp = "00"
        report "DMI resp /= OK on addr 0x" & to_hstring(a) severity failure;
      data := dmi_rdata;
      wait until rising_edge(clk);
    end procedure;

    procedure dmi_write(a : std_logic_vector(6 downto 0);
                        d : std_logic_vector(31 downto 0)) is
      variable dummy : std_logic_vector(31 downto 0);
    begin
      dmi_xact(a, d, "10", dummy);
    end procedure;

    procedure dmi_read(a : std_logic_vector(6 downto 0);
                       data : out std_logic_vector(31 downto 0)) is
    begin
      dmi_xact(a, x"00000000", "01", data);
    end procedure;

    procedure wait_cmd_done is
      variable r : std_logic_vector(31 downto 0);
    begin
      for i in 0 to 200 loop
        dmi_read(A_ABSTRACTCS, r);
        exit when r(12) = '0';   -- busy
        if i = 200 then
          report "abstract command stuck busy" severity failure;
        end if;
      end loop;
      assert r(10 downto 8) = "000"
        report "abstract cmderr /= 0, ABSTRACTCS=0x" & to_hstring(r)
        severity failure;
    end procedure;

    -- Read GPR x<regno> (5-bit) via abstract command (aarsize=2) -> DATA0.
    procedure read_gpr(regno : natural; data : out std_logic_vector(31 downto 0)) is
      variable cmd : std_logic_vector(31 downto 0);
    begin
      -- cmdtype=0, aarsize=2 (bit22:20=010), transfer=1 (bit17), write=0,
      -- regno = 0x1000 + regno
      cmd := x"00221000" or std_logic_vector(to_unsigned(regno, 32));
      dmi_write(A_COMMAND, cmd);
      wait_cmd_done;
      dmi_read(A_DATA0, data);
    end procedure;

    -- Read dpc (CSR 0x7B1) via abstract command (aarsize=3) -> DATA0/DATA1.
    procedure read_dpc(lo : out std_logic_vector(31 downto 0);
                       hi : out std_logic_vector(31 downto 0)) is
    begin
      dmi_write(A_COMMAND, x"003207B1");   -- read dpc, aarsize=3
      wait_cmd_done;
      dmi_read(A_DATA0, lo);
      dmi_read(A_DATA1, hi);
    end procedure;
  begin
    -- Reset
    rst_n <= '0';
    for i in 0 to 8 loop wait until rising_edge(clk); end loop;
    rst_n <= '1';
    for i in 0 to 8 loop wait until rising_edge(clk); end loop;

    dmi_write(A_DMCONTROL, x"00000001");   -- dmactive=1

    --------------------------------------------------------------------------
    -- STAGE A: SBA system-bus write + readback through the glue.
    --------------------------------------------------------------------------
    dmi_write(A_SBCS, x"00040000");        -- sbaccess=2 (32-bit)
    dmi_write(A_SBADDRESS0, x"00000024");
    dmi_write(A_SBDATA0, x"CAFEBABE");     -- bus write
    dmi_write(A_SBCS, x"00140000");        -- sbreadonaddr=1, sbaccess=2
    dmi_write(A_SBADDRESS0, x"00000024");  -- triggers a read
    dmi_read(A_SBDATA0, rd);
    assert rd = x"CAFEBABE"
      report "STAGE A FAIL: SBA readback /= CAFEBABE, got 0x" & to_hstring(rd)
      severity failure;
    report "HART-INT STAGE A PASS: DM SBA write+readback through glue (wrapper mem)"
      severity note;

    --------------------------------------------------------------------------
    -- STAGE B: single-step FROM RESET over the first instruction
    -- (addi x10,x0,42) — proves a step both advances pc by one insn AND
    -- updates an x-register (a0: 0 -> 42).  Must run while the hart is still at
    -- pc=0 (before the free-run stage consumes the addi's).
    --------------------------------------------------------------------------
    assert o_halted = '1'
      report "STAGE B FAIL: hart not halted at reset" severity failure;
    read_gpr(10, rd);                      -- baseline a0 at reset
    assert rd = x"00000000"
      report "STAGE B FAIL: a0 not 0 at reset, got 0x" & to_hstring(rd)
      severity failure;
    read_dpc(dpc_lo, dpc_hi);
    pc_before := unsigned(dpc_lo);
    -- dcsr.step = 1
    dmi_write(A_DATA0, x"00000007");       -- step=1, prv=3
    dmi_write(A_COMMAND, x"002307B0");     -- write dcsr, aarsize=2
    wait_cmd_done;
    dmi_write(A_DMCONTROL, x"40000001");   -- resumereq=1 (single step)
    for i in 0 to 40 loop
      dmi_read(A_DMSTATUS, rd);
      exit when rd(9) = '1';               -- allhalted (re-halted after 1 insn)
      if i = 40 then
        report "STAGE B FAIL: hart did not re-halt after step-from-reset"
          severity failure;
      end if;
    end loop;
    read_dpc(dpc_lo, dpc_hi);
    pc_after := unsigned(dpc_lo);
    read_gpr(10, rd);                      -- a0 after the stepped addi
    write(l, string'("  step-from-reset: pc 0x")); hwrite(l, std_logic_vector(pc_before));
    write(l, string'(" -> 0x")); hwrite(l, std_logic_vector(pc_after));
    write(l, string'(", a0 0 -> ")); write(l, to_integer(unsigned(rd)));
    writeline(output, l);
    assert (pc_after - pc_before) = 4
      report "STAGE B FAIL: step advanced pc by "
             & integer'image(to_integer(pc_after - pc_before)) & " (expected 4)"
      severity failure;
    assert rd = x"0000002A"
      report "STAGE B FAIL: step did not update x10 (a0) to 42, got 0x"
             & to_hstring(rd) severity failure;
    -- Clear dcsr.step for the free-run stage.
    dmi_write(A_DATA0, x"00000003");       -- step=0, prv=3
    dmi_write(A_COMMAND, x"002307B0");
    wait_cmd_done;
    report "HART-INT STAGE B PASS: single-step retired one insn (pc += 4) AND "
           & "updated x10 (a0: 0 -> 42)" severity note;

    --------------------------------------------------------------------------
    -- STAGE C: resume the REAL hart -> it free-runs -> haltreq halts it.
    --------------------------------------------------------------------------
    dmi_write(A_DMCONTROL, x"40000001");   -- resumereq=1 (dcsr.step=0 -> free run)
    -- Let the hart execute the second addi + NOP sled (ra=7 by ~cyc4).
    for i in 0 to 40 loop wait until rising_edge(clk); end loop;
    assert o_core_run = '1'
      report "STAGE C FAIL: core not running after resume" severity failure;
    dmi_write(A_DMCONTROL, x"80000001");   -- haltreq=1
    for i in 0 to 10 loop wait until rising_edge(clk); end loop;
    assert o_halted = '1'
      report "STAGE C FAIL: hart did not halt on haltreq" severity failure;
    report "HART-INT STAGE C PASS: resume -> real hart free-ran -> haltreq halted it"
      severity note;

    --------------------------------------------------------------------------
    -- STAGE D: abstract-command GPR readback of REAL computed values.
    --------------------------------------------------------------------------
    read_gpr(10, rd);                      -- x10 = a0
    assert rd = x"0000002A"
      report "STAGE D FAIL: x10 (a0) /= 42, got 0x" & to_hstring(rd)
      severity failure;
    write(l, string'("  abstract read x10 (a0) = ")); write(l, to_integer(unsigned(rd)));
    writeline(output, l);
    read_gpr(1, rd);                       -- x1 = ra
    assert rd = x"00000007"
      report "STAGE D FAIL: x1 (ra) /= 7, got 0x" & to_hstring(rd)
      severity failure;
    write(l, string'("  abstract read x1  (ra) = ")); write(l, to_integer(unsigned(rd)));
    writeline(output, l);
    -- Cross-check against the wrapper's observation of the real core registers.
    assert o_dbg_a0 = x"2A" and o_dbg_ra = x"0007"
      report "STAGE D FAIL: observed core regs disagree with abstract read"
      severity failure;
    report "HART-INT STAGE D PASS: abstract-cmd GPR readback x10==42, x1==7 (real hart)"
      severity note;

    --------------------------------------------------------------------------
    -- STAGE E: single-step in the NOP sled -> clean pc += 4 (pc-advance only).
    --------------------------------------------------------------------------
    read_dpc(dpc_lo, dpc_hi);
    pc_before := unsigned(dpc_lo);
    dmi_write(A_DATA0, x"00000007");       -- step=1, prv=3
    dmi_write(A_COMMAND, x"002307B0");     -- write dcsr, aarsize=2
    wait_cmd_done;
    dmi_write(A_DMCONTROL, x"40000001");   -- resumereq=1 (single step)
    for i in 0 to 40 loop
      dmi_read(A_DMSTATUS, rd);
      exit when rd(9) = '1';               -- allhalted
      if i = 40 then
        report "STAGE E FAIL: hart did not re-halt after single step" severity failure;
      end if;
    end loop;
    read_dpc(dpc_lo, dpc_hi);
    pc_after := unsigned(dpc_lo);
    write(l, string'("  step (NOP sled): pc 0x")); hwrite(l, std_logic_vector(pc_before));
    write(l, string'(" -> 0x")); hwrite(l, std_logic_vector(pc_after));
    writeline(output, l);
    assert (pc_after - pc_before) = 4
      report "STAGE E FAIL: single step advanced pc by "
             & integer'image(to_integer(pc_after - pc_before)) & " (expected 4)"
      severity failure;
    report "HART-INT STAGE E PASS: single-step retired exactly one instruction (pc += 4)"
      severity note;

    report "JTAG HART E2E: ALL PASS" severity note;
    stop;
  end process;
end architecture sim;
