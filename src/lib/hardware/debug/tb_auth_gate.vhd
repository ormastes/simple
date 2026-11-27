-- tb_auth_gate.vhd — debug-authentication gate testbench (bug
-- riscv_debug_module_authenticated_hardwired_2026-09-01).
--
-- Before the fix, debug_registers.vhd hard-wired dmstatus.authenticated = 1
-- and the System Bus Access engine answered any JTAG connection with full
-- system-memory read/write. This testbench proves the gate that replaced
-- the constant:
--
--   CHECK1:  after dmactive=1, dmstatus.authenticated = 0 (computed state,
--            not a constant) and authbusy = 0.
--   CHECK2:  NEGATIVE GATE — while unauthenticated, an SBA write trigger
--            (SBDATA0) is denied: sb_we_o never asserts, sberror = 7
--            (other: access denied), memory unchanged.
--   CHECK3:  wrong authdata response keeps the DM unauthenticated
--            (authbusy observable, then clears on dmstatus read).
--   CHECK4:  correct authdata response authenticates; SBA read works and
--            reads back the sba_test_mem init pattern — also proving the
--            denied CHECK2 write never reached the bus.
--   CHECK5:  a later wrong response DE-authenticates (state is computed per
--            challenge, not sticky-once-true) and SBA is denied again.
--   CHECK6:  dmactive=0 resets authentication; a new session starts
--            unauthenticated and SBA stays denied until re-auth.
--   CHECK7:  lifecycle fuse = LOCKED forces authenticated = 0 even for the
--            correct key, and SBA is denied.
--   CHECK8:  lifecycle fuse = OPEN (unprovisioned development state)
--            authenticates without a challenge and SBA works.
--
-- Prints "AUTH GATE PASS" only if every assert held.
--
-- Lifecycle encoding (fuse/OTP inputs, see debug_registers.vhd):
--   "00" OPEN         — unprovisioned: debug open (fab/development)
--   "01" PROVISIONED  — challenge/response via authdata (0x30) vs OTP key
--   "10" LOCKED       — debug disabled; challenge ignored
--   "11" reserved     — treated as LOCKED
--
-- Auth flow (PROVISIONED): debugger writes the response to AUTHDATA
-- (DMI 0x30); the DM compares it against auth_key_i (OTP). Match ->
-- authenticated; mismatch -> unauthenticated. dmstatus.authbusy is set by
-- an authdata write and clears on the next dmstatus read. Authentication
-- (and all other DM state) resets on dmactive=0 or rst.

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use std.env.all;

entity tb_auth_gate is
end entity;

architecture sim of tb_auth_gate is

  constant CLK_PERIOD : time := 10 ns;

  signal clk   : std_logic := '0';
  signal rst_n : std_logic := '0';

  -- DMI request side (into dmi_bus)
  signal dmi_valid : std_logic := '0';
  signal dmi_addr  : std_logic_vector(6 downto 0) := (others => '0');
  signal dmi_wdata : std_logic_vector(31 downto 0) := (others => '0');
  signal dmi_op    : std_logic_vector(1 downto 0) := "00";
  signal dmi_rdata : std_logic_vector(31 downto 0);
  signal dmi_resp  : std_logic_vector(1 downto 0);
  signal dmi_ready : std_logic;

  -- dmi_bus <-> DM
  signal dm_valid, dm_ready : std_logic;
  signal dm_addr  : std_logic_vector(6 downto 0);
  signal dm_wdata : std_logic_vector(31 downto 0);
  signal dm_op    : std_logic_vector(1 downto 0);
  signal dm_rdata : std_logic_vector(31 downto 0);
  signal dm_resp  : std_logic_vector(1 downto 0);

  -- SBA bus
  signal sb_re    : std_logic;
  signal sb_we    : std_logic;
  signal sb_addr  : std_logic_vector(63 downto 0);
  signal sb_wdata : std_logic_vector(63 downto 0);
  signal sb_size  : std_logic_vector(1 downto 0);
  signal sb_rdata : std_logic_vector(63 downto 0);
  signal sb_ack   : std_logic;
  signal sb_err   : std_logic;

  -- Fuse/OTP model inputs
  signal lifecycle : std_logic_vector(1 downto 0) := "01";  -- PROVISIONED
  constant AUTH_KEY : std_logic_vector(31 downto 0) := x"A5A55A5A";

  constant A_DMCONTROL  : std_logic_vector(6 downto 0) := "0010000";  -- 0x10
  constant A_DMSTATUS   : std_logic_vector(6 downto 0) := "0010001";  -- 0x11
  constant A_AUTHDATA   : std_logic_vector(6 downto 0) := "0110000";  -- 0x30
  constant A_SBCS       : std_logic_vector(6 downto 0) := "0111000";  -- 0x38
  constant A_SBADDRESS0 : std_logic_vector(6 downto 0) := "0111001";  -- 0x39
  constant A_SBDATA0    : std_logic_vector(6 downto 0) := "0111100";  -- 0x3C
  constant A_SBDATA1    : std_logic_vector(6 downto 0) := "0111101";  -- 0x3D

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
      halted_i => '1', running_i => '0',
      lifecycle_i => lifecycle,
      auth_key_i  => AUTH_KEY,
      sb_re_o => sb_re, sb_we_o => sb_we,
      sb_addr_o => sb_addr, sb_wdata_o => sb_wdata, sb_size_o => sb_size,
      sb_rdata_i => sb_rdata, sb_ack_i => sb_ack, sb_err_i => sb_err);

  u_mem : entity work.sba_test_mem
    generic map (ACK_DELAY => 8)
    port map (
      clk => clk, rst_n => rst_n,
      sb_re_i => sb_re, sb_we_i => sb_we,
      sb_addr_i => sb_addr, sb_wdata_i => sb_wdata, sb_size_i => sb_size,
      sb_rdata_o => sb_rdata, sb_ack_o => sb_ack, sb_err_o => sb_err);

  stim : process
    variable rd : std_logic_vector(31 downto 0);
    variable sbcs : std_logic_vector(31 downto 0);

    -- One DMI transaction through dmi_bus (same harness as tb_sba).
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

    -- Poll SBCS until sbbusy(21) = 0; returns the final SBCS value.
    procedure wait_sb_done(variable sbcs_out : out std_logic_vector(31 downto 0)) is
      variable r : std_logic_vector(31 downto 0) := (others => '0');
    begin
      for i in 0 to 63 loop
        dmi_read(A_SBCS, r);
        exit when r(21) = '0';
      end loop;
      sbcs_out := r;
    end procedure wait_sb_done;

    -- Assert that no SBA bus access starts for the next n clocks.
    procedure assert_no_bus_activity(n : natural) is
    begin
      for i in 1 to n loop
        wait until rising_edge(clk);
        assert sb_re = '0' and sb_we = '0'
          report "SBA bus access started while unauthenticated"
          severity failure;
      end loop;
    end procedure assert_no_bus_activity;

    -- Attempt a 32-bit SBA write at the current SBADDRESS; assert it is
    -- denied (no bus activity, sberror = 7), then W1C sberror while
    -- preserving sbaccess=2 (reset capability value).
    procedure attempt_sba_write_denied is
      variable sbcs : std_logic_vector(31 downto 0);
    begin
      dmi_write(A_SBDATA0, x"DEADBEEF");
      assert_no_bus_activity(12);  -- > ACK_DELAY: a real access would show
      dmi_read(A_SBCS, sbcs);
      assert sbcs(14 downto 12) = "111"
        report "CHECK-deny FAIL: unauthenticated SBA write not denied, SBCS=0x"
          & to_hstring(sbcs) severity failure;
      assert sbcs(21) = '0'
        report "CHECK-deny FAIL: sbbusy stuck after denied write, SBCS=0x"
          & to_hstring(sbcs) severity failure;
      dmi_write(A_SBCS, x"00047000");  -- W1C sberror, keep sbaccess=2
      dmi_read(A_SBCS, sbcs);
      assert sbcs(14 downto 12) = "000"
        report "CHECK-deny FAIL: sberror not W1C-cleared, SBCS=0x"
          & to_hstring(sbcs) severity failure;
    end procedure attempt_sba_write_denied;

  begin
    -- Reset
    rst_n <= '0';
    wait for 5 * CLK_PERIOD;
    rst_n <= '1';
    wait for 2 * CLK_PERIOD;

    ---------------------------------------------------------------------
    -- Activate the DM (dmactive=1).
    dmi_write(A_DMCONTROL, x"00000001");
    dmi_read(A_DMCONTROL, rd);
    assert rd(0) = '1'
      report "dmactive did not read back 1" severity failure;

    ---------------------------------------------------------------------
    -- CHECK1: authenticated is a computed state: 0 after activation.
    dmi_read(A_DMSTATUS, rd);
    assert rd(3 downto 0) = "0010"
      report "CHECK1 FAIL: DMSTATUS.version /= 2, got 0x" & to_hstring(rd)
      severity failure;
    assert rd(7) = '0'
      report "CHECK1 FAIL: authenticated hard-wired 1 (no auth unit), DMSTATUS=0x"
        & to_hstring(rd) severity failure;
    assert rd(6) = '0'
      report "CHECK1 FAIL: authbusy set without authdata write, DMSTATUS=0x"
        & to_hstring(rd) severity failure;
    report "CHECK1 PASS: authenticated=0, authbusy=0 after activation"
      severity note;

    ---------------------------------------------------------------------
    -- CHECK2: NEGATIVE GATE — unauthenticated SBA is denied.
    -- Non-vacuous: a sabotaged auth check (gate always open) fails here.
    dmi_write(A_SBADDRESS0, x"00000010");
    attempt_sba_write_denied;
    report "CHECK2 PASS: unauthenticated SBA write denied (sberror=7, no bus activity)"
      severity note;

    ---------------------------------------------------------------------
    -- CHECK3: wrong authdata response keeps the DM unauthenticated.
    dmi_write(A_AUTHDATA, AUTH_KEY xor x"00000001");
    dmi_read(A_DMSTATUS, rd);
    assert rd(7) = '0'
      report "CHECK3 FAIL: wrong key authenticated, DMSTATUS=0x" & to_hstring(rd)
      severity failure;
    assert rd(6) = '1'
      report "CHECK3 FAIL: authbusy not set by authdata write, DMSTATUS=0x"
        & to_hstring(rd) severity failure;
    dmi_read(A_DMSTATUS, rd);  -- second read clears authbusy
    assert rd(6) = '0'
      report "CHECK3 FAIL: authbusy not cleared by dmstatus read, DMSTATUS=0x"
        & to_hstring(rd) severity failure;
    assert rd(7) = '0'
      report "CHECK3 FAIL: wrong key authenticated, DMSTATUS=0x" & to_hstring(rd)
      severity failure;
    attempt_sba_write_denied;  -- still gated
    report "CHECK3 PASS: wrong key rejected, authbusy visible, SBA still denied"
      severity note;

    ---------------------------------------------------------------------
    -- CHECK4: correct response authenticates; SBA works.
    dmi_write(A_AUTHDATA, AUTH_KEY);
    dmi_read(A_DMSTATUS, rd);
    assert rd(7) = '1'
      report "CHECK4 FAIL: correct key not authenticated, DMSTATUS=0x"
        & to_hstring(rd) severity failure;
    -- 64-bit read at 0x10 via sbreadonaddr (same as tb_sba CHECK2).
    dmi_write(A_SBCS, x"00160000");  -- sbreadonaddr=1, sbaccess=3 (64-bit)
    dmi_write(A_SBADDRESS0, x"00000010");
    wait_sb_done(sbcs);
    assert sbcs(14 downto 12) = "000" and sbcs(22) = '0'
      report "CHECK4 FAIL: authenticated SBA read raised error, SBCS=0x"
        & to_hstring(sbcs) severity failure;
    dmi_read(A_SBDATA0, rd);
    assert rd = x"00020002"
      report "CHECK4 FAIL: SBDATA0 /= mem[0x10] low, got 0x" & to_hstring(rd)
      severity failure;
    dmi_read(A_SBDATA1, rd);
    assert rd = x"A5A50000"
      report "CHECK4 FAIL: SBDATA1 /= mem[0x10] high, got 0x" & to_hstring(rd)
      severity failure;
    report "CHECK4 PASS: correct key authenticated; SBA read back init pattern"
      severity note;

    ---------------------------------------------------------------------
    -- CHECK5: a later wrong response DE-authenticates; SBA denied again.
    dmi_write(A_AUTHDATA, x"FFFFFFFF");
    dmi_read(A_DMSTATUS, rd);
    assert rd(7) = '0'
      report "CHECK5 FAIL: authenticated state sticky after wrong key, DMSTATUS=0x"
        & to_hstring(rd) severity failure;
    attempt_sba_write_denied;
    report "CHECK5 PASS: re-challenge with wrong key de-authenticates; SBA denied"
      severity note;

    ---------------------------------------------------------------------
    -- CHECK6: dmactive=0 resets authentication.
    dmi_write(A_AUTHDATA, AUTH_KEY);
    dmi_read(A_DMSTATUS, rd);
    assert rd(7) = '1'
      report "CHECK6 FAIL: re-auth before dmactive reset failed, DMSTATUS=0x"
        & to_hstring(rd) severity failure;
    dmi_write(A_DMCONTROL, x"00000000");  -- dmactive=0: full DM reset
    dmi_read(A_DMSTATUS, rd);
    assert rd(7) = '0'
      report "CHECK6 FAIL: authenticated survived dmactive=0, DMSTATUS=0x"
        & to_hstring(rd) severity failure;
    dmi_write(A_DMCONTROL, x"00000001");  -- re-activate
    dmi_read(A_DMSTATUS, rd);
    assert rd(7) = '0'
      report "CHECK6 FAIL: authenticated after fresh session, DMSTATUS=0x"
        & to_hstring(rd) severity failure;
    attempt_sba_write_denied;
    report "CHECK6 PASS: dmactive=0 clears authentication; new session starts gated"
      severity note;

    ---------------------------------------------------------------------
    -- CHECK7: LOCKED lifecycle forces authenticated=0 even with the key.
    lifecycle <= "10";
    wait for 3 * CLK_PERIOD;
    dmi_write(A_AUTHDATA, AUTH_KEY);  -- correct key, but locked
    dmi_read(A_DMSTATUS, rd);
    assert rd(7) = '0'
      report "CHECK7 FAIL: LOCKED lifecycle authenticated, DMSTATUS=0x"
        & to_hstring(rd) severity failure;
    attempt_sba_write_denied;
    report "CHECK7 PASS: LOCKED lifecycle keeps SBA denied (challenge ignored)"
      severity note;

    ---------------------------------------------------------------------
    -- CHECK8: OPEN lifecycle authenticates without a challenge.
    lifecycle <= "00";
    wait for 3 * CLK_PERIOD;
    dmi_read(A_DMSTATUS, rd);
    assert rd(7) = '1'
      report "CHECK8 FAIL: OPEN lifecycle not authenticated, DMSTATUS=0x"
        & to_hstring(rd) severity failure;
    dmi_write(A_SBCS, x"00160000");  -- sbreadonaddr=1, sbaccess=3 (64-bit)
    dmi_write(A_SBADDRESS0, x"00000010");
    wait_sb_done(sbcs);
    assert sbcs(14 downto 12) = "000" and sbcs(22) = '0'
      report "CHECK8 FAIL: OPEN-lifecycle SBA read raised error, SBCS=0x"
        & to_hstring(sbcs) severity failure;
    dmi_read(A_SBDATA0, rd);
    assert rd = x"00020002"
      report "CHECK8 FAIL: OPEN SBA read wrong data, got 0x" & to_hstring(rd)
      severity failure;
    report "CHECK8 PASS: OPEN lifecycle authenticated; SBA open (development state)"
      severity note;

    ---------------------------------------------------------------------
    report "AUTH GATE PASS" severity note;
    finish;
  end process;

end architecture sim;
