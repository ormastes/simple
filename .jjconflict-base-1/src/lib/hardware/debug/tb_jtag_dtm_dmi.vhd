-- tb_jtag_dtm_dmi.vhd — GHDL testbench for Stage 1 JTAG debug (TAP + DTM + DMI).
--
-- Acceptance checks (each backed by `assert ... severity failure`):
--   1. TAP reaches Test-Logic-Reset after 5 TMS=1 clocks (from Shift-DR).
--   2. IDCODE instruction + 32-bit DR scan returns 0x15350067.
--   3. DTMCS scan reports version=1 (bits 3:0) and abits=7 (bits 9:4).
--   4. DMI write to addr 0x03 then DMI read returns the data, resp=success.
--   5. BYPASS is 1 bit: pattern shifted through comes back delayed 1 cycle.
--   6. (Stage 5) DTMCS busy semantics: a stall bridge delays the DMI target
--      by `stall_cycles`, so a DMI scan while the request is in flight
--      captures op=3 (busy) and sets sticky dmistat=3; DTMCS.dmireset
--      clears it and a fresh round-trip succeeds.
--
-- Prints "JTAG STAGE1 PASS" only if every assert held.
--
-- TB drives TMS/TDI during the TCK-low phase and samples TDO during the
-- TCK-low phase (after the falling edge), per IEEE 1149.1 timing.

library ieee;
use ieee.std_logic_1164.all;
use std.env.all;

entity tb_jtag_dtm_dmi is
end entity tb_jtag_dtm_dmi;

architecture sim of tb_jtag_dtm_dmi is

  constant EXPECTED_IDCODE : std_logic_vector(31 downto 0) := x"15350067";

  signal tck    : std_logic := '0';
  signal tms    : std_logic := '0';
  signal tdi    : std_logic := '0';
  signal trst_n : std_logic := '0';
  signal tdo    : std_logic;
  signal tlr_o  : std_logic;

  signal sel_dtmcs, sel_dmi                 : std_logic;
  signal capture_en, shift_en, update_en    : std_logic;
  signal dr_tdi                             : std_logic;
  signal dtmcs_tdo, dmi_tdo                 : std_logic;

  signal dmi_valid : std_logic;
  signal dmi_addr  : std_logic_vector(6 downto 0);
  signal dmi_wdata : std_logic_vector(31 downto 0);
  signal dmi_op    : std_logic_vector(1 downto 0);
  signal dmi_rdata : std_logic_vector(31 downto 0);
  signal dmi_resp  : std_logic_vector(1 downto 0);
  signal dmi_ready : std_logic;

  -- Stage-5 stall bridge (DTM -> dmi_bus): latches each DMI request and
  -- forwards it after `stall_cycles` TCK cycles, so the DTM's busy/sticky
  -- dmistat path gets a real window. stall_cycles=0 adds one fixed cycle
  -- of latency, which the earlier checks absorb in their idle_cycles.
  signal b_valid      : std_logic := '0';
  signal b_addr       : std_logic_vector(6 downto 0) := (others => '0');
  signal b_wdata      : std_logic_vector(31 downto 0) := (others => '0');
  signal b_op         : std_logic_vector(1 downto 0) := "00";
  signal stall_cycles : natural := 0;

begin

  u_tap : entity work.jtag_tap
    generic map (IDCODE_VALUE => EXPECTED_IDCODE)
    port map (
      tck => tck, tms => tms, tdi => tdi, trst_n => trst_n, tdo => tdo,
      tlr_o => tlr_o,
      sel_dtmcs => sel_dtmcs, sel_dmi => sel_dmi,
      capture_en => capture_en, shift_en => shift_en, update_en => update_en,
      dr_tdi => dr_tdi, dtmcs_tdo => dtmcs_tdo, dmi_tdo => dmi_tdo);

  u_dtm : entity work.riscv_dtm
    port map (
      tck => tck, trst_n => trst_n,
      tlr => tlr_o,
      sel_dtmcs => sel_dtmcs, sel_dmi => sel_dmi,
      capture_en => capture_en, shift_en => shift_en, update_en => update_en,
      tdi => dr_tdi, dtmcs_tdo => dtmcs_tdo, dmi_tdo => dmi_tdo,
      dmi_valid => dmi_valid, dmi_addr => dmi_addr, dmi_wdata => dmi_wdata,
      dmi_op => dmi_op, dmi_rdata => dmi_rdata, dmi_resp => dmi_resp,
      dmi_ready => dmi_ready);

  u_dmi : entity work.dmi_bus
    port map (
      clk => tck, rst_n => trst_n,
      valid => b_valid, addr => b_addr, wdata => b_wdata, op => b_op,
      rdata => dmi_rdata, resp => dmi_resp, ready => dmi_ready);

  -- Stall bridge: request path is delayed, response path is direct.
  bridge : process (tck, trst_n)
    variable pend : boolean := false;
    variable cnt  : natural := 0;
  begin
    if trst_n = '0' then
      b_valid <= '0';
      pend := false;
      cnt := 0;
    elsif rising_edge(tck) then
      b_valid <= '0';
      if dmi_valid = '1' then
        b_addr  <= dmi_addr;
        b_wdata <= dmi_wdata;
        b_op    <= dmi_op;
        pend := true;
        cnt := stall_cycles;
      elsif pend then
        if cnt = 0 then
          b_valid <= '1';
          pend := false;
        else
          cnt := cnt - 1;
        end if;
      end if;
    end if;
  end process bridge;

  stim : process

    -- One full TCK cycle: set TMS/TDI in the low phase, rise, fall.
    -- After return, TDO holds the value registered on the falling edge.
    procedure jtag_cycle(tms_v : std_logic; tdi_v : std_logic) is
    begin
      tms <= tms_v;
      tdi <= tdi_v;
      wait for 5 ns;          -- setup during TCK low
      tck <= '1';
      wait for 10 ns;         -- TCK high phase
      tck <= '0';
      wait for 5 ns;          -- TCK low tail: TDO updated by falling edge
    end procedure;

    procedure idle_cycles(n : natural) is
    begin
      for k in 1 to n loop
        jtag_cycle('0', '0'); -- stay in Run-Test/Idle
      end loop;
    end procedure;

    -- Full DR scan from Run-Test/Idle back to Run-Test/Idle.
    -- din/dout indexed (N-1 downto 0); bit 0 is shifted first (LSB-first).
    procedure scan_dr(din : in std_logic_vector;
                      dout : out std_logic_vector) is
    begin
      jtag_cycle('1', '0');   -- RTI -> Select-DR
      jtag_cycle('0', '0');   -- Select-DR -> Capture-DR
      jtag_cycle('0', '0');   -- Capture-DR -> Shift-DR (capture happens here)
      for i in 0 to din'length - 1 loop
        dout(i) := tdo;       -- captured bit i, valid during TCK low
        if i = din'length - 1 then
          jtag_cycle('1', din(i));  -- last shift, exit to Exit1-DR
        else
          jtag_cycle('0', din(i));
        end if;
      end loop;
      jtag_cycle('1', '0');   -- Exit1-DR -> Update-DR
      jtag_cycle('0', '0');   -- Update-DR -> RTI (update happens here)
    end procedure;

    -- Full IR scan from Run-Test/Idle back to Run-Test/Idle. LSB-first.
    procedure scan_ir(insn : in std_logic_vector(4 downto 0)) is
    begin
      jtag_cycle('1', '0');   -- RTI -> Select-DR
      jtag_cycle('1', '0');   -- Select-DR -> Select-IR
      jtag_cycle('0', '0');   -- Select-IR -> Capture-IR
      jtag_cycle('0', '0');   -- Capture-IR -> Shift-IR
      for i in 0 to 4 loop
        if i = 4 then
          jtag_cycle('1', insn(i));
        else
          jtag_cycle('0', insn(i));
        end if;
      end loop;
      jtag_cycle('1', '0');   -- Exit1-IR -> Update-IR
      jtag_cycle('0', '0');   -- Update-IR -> RTI
    end procedure;

    -- din vectors must carry explicit (N-1 downto 0) ranges: scan_dr indexes
    -- din(0) as the first (LSB) bit, but a bare string literal would bind to
    -- the unconstrained formal with an ascending (0 to N-1) range.
    variable din32  : std_logic_vector(31 downto 0) := (others => '0');
    variable din4   : std_logic_vector(3 downto 0)  := "0001";
    variable dout32 : std_logic_vector(31 downto 0);
    variable dout41 : std_logic_vector(40 downto 0);
    variable dout4  : std_logic_vector(3 downto 0);
    variable din41  : std_logic_vector(40 downto 0);

    constant TEST_ADDR : std_logic_vector(6 downto 0)  := "0000011";  -- 0x03
    constant TEST_DATA : std_logic_vector(31 downto 0) := x"DEADBEEF";

  begin
    -- Reset
    trst_n <= '0';
    wait for 20 ns;
    trst_n <= '1';
    wait for 20 ns;

    ---------------------------------------------------------------------
    -- Check 1: TLR after 5 TMS=1 clocks, starting from Shift-DR.
    ---------------------------------------------------------------------
    jtag_cycle('0', '0');     -- TLR -> RTI
    jtag_cycle('1', '0');     -- RTI -> Select-DR
    jtag_cycle('0', '0');     -- -> Capture-DR
    jtag_cycle('0', '0');     -- -> Shift-DR
    for k in 1 to 5 loop
      jtag_cycle('1', '0');   -- Shift->Exit1->Update->SelDR->SelIR->TLR
    end loop;
    assert tlr_o = '1'
      report "CHECK1 FAIL: TAP not in Test-Logic-Reset after 5 TMS=1 clocks"
      severity failure;
    report "CHECK1 PASS: Test-Logic-Reset reached after 5 TMS=1 clocks"
      severity note;
    jtag_cycle('0', '0');     -- TLR -> RTI

    ---------------------------------------------------------------------
    -- Check 2: IDCODE scan.
    ---------------------------------------------------------------------
    scan_ir("00001");         -- IDCODE
    scan_dr(din32, dout32);
    assert dout32 = EXPECTED_IDCODE
      report "CHECK2 FAIL: IDCODE mismatch, got " & to_hstring(dout32)
      severity failure;
    report "CHECK2 PASS: IDCODE = 0x" & to_hstring(dout32) severity note;

    ---------------------------------------------------------------------
    -- Check 3: DTMCS version=1, abits=7.
    ---------------------------------------------------------------------
    scan_ir("10000");         -- DTMCS
    scan_dr(din32, dout32);
    assert dout32(3 downto 0) = "0001"
      report "CHECK3 FAIL: DTMCS version /= 1, got " & to_hstring(dout32)
      severity failure;
    assert dout32(9 downto 4) = "000111"
      report "CHECK3 FAIL: DTMCS abits /= 7, got " & to_hstring(dout32)
      severity failure;
    report "CHECK3 PASS: DTMCS = 0x" & to_hstring(dout32)
      & " (version=1, abits=7)" severity note;

    ---------------------------------------------------------------------
    -- Check 4: DMI write then read round-trip.
    ---------------------------------------------------------------------
    scan_ir("10001");         -- DMI
    din41 := TEST_ADDR & TEST_DATA & "10";      -- op=2 write
    scan_dr(din41, dout41);
    idle_cycles(8);
    din41 := TEST_ADDR & x"00000000" & "01";    -- op=1 read
    scan_dr(din41, dout41);
    idle_cycles(8);
    din41 := (others => '0');                   -- op=0 nop: collect result
    scan_dr(din41, dout41);
    assert dout41(1 downto 0) = "00"
      report "CHECK4 FAIL: DMI op status /= success, got op="
        & to_string(dout41(1 downto 0))
      severity failure;
    assert dout41(33 downto 2) = TEST_DATA
      report "CHECK4 FAIL: DMI readback mismatch, got 0x"
        & to_hstring(dout41(33 downto 2))
      severity failure;
    report "CHECK4 PASS: DMI write/read round-trip addr=0x03 data=0x"
      & to_hstring(dout41(33 downto 2)) & " resp=success" severity note;

    ---------------------------------------------------------------------
    -- Check 5: BYPASS is exactly 1 bit (1-cycle delay).
    ---------------------------------------------------------------------
    scan_ir("11111");         -- BYPASS
    scan_dr(din4, dout4);     -- shift in 1,0,0,0 (LSB first)
    -- expected out: captured '0', then input delayed 1 bit -> "0010"
    assert dout4 = "0010"
      report "CHECK5 FAIL: BYPASS not 1-bit delay, got "
        & to_string(dout4)
      severity failure;
    report "CHECK5 PASS: BYPASS 1-bit passthrough (out=" & to_string(dout4)
      & ")" severity note;

    ---------------------------------------------------------------------
    -- Check 6 (Stage 5): DTMCS busy semantics — sticky dmistat=3 + dmireset.
    ---------------------------------------------------------------------
    scan_ir("10001");         -- DMI
    stall_cycles <= 100;      -- DM ack delayed: next scan sees busy
    din41 := "0000010" & x"00000000" & "01";    -- read scratch 0x02
    scan_dr(din41, dout41);   -- request issued at Update-DR, now in flight
    din41 := (others => '0');                   -- nop: collect while busy
    scan_dr(din41, dout41);
    assert dout41(1 downto 0) = "11"
      report "CHECK6 FAIL: DMI capture while busy /= op 3, got op="
        & to_string(dout41(1 downto 0))
      severity failure;
    stall_cycles <= 0;
    idle_cycles(120);         -- let the stalled request complete
    scan_ir("10000");         -- DTMCS
    scan_dr(din32, dout32);
    assert dout32(11 downto 10) = "11"
      report "CHECK6 FAIL: sticky dmistat /= 3 after busy hit, DTMCS=0x"
        & to_hstring(dout32)
      severity failure;
    din32(16) := '1';         -- dmireset
    scan_dr(din32, dout32);
    din32 := (others => '0');
    scan_dr(din32, dout32);
    assert dout32(11 downto 10) = "00"
      report "CHECK6 FAIL: dmistat not cleared by dmireset, DTMCS=0x"
        & to_hstring(dout32)
      severity failure;
    scan_ir("10001");         -- DMI: fresh round-trip must succeed
    din41 := TEST_ADDR & x"00000000" & "01";
    scan_dr(din41, dout41);
    idle_cycles(8);
    din41 := (others => '0');
    scan_dr(din41, dout41);
    assert dout41(1 downto 0) = "00" and dout41(33 downto 2) = TEST_DATA
      report "CHECK6 FAIL: post-dmireset DMI read broken, op="
        & to_string(dout41(1 downto 0)) & " data=0x"
        & to_hstring(dout41(33 downto 2))
      severity failure;
    report "CHECK6 PASS: busy capture op=3, sticky dmistat=3, dmireset recovers"
      severity note;

    ---------------------------------------------------------------------
    report "JTAG STAGE1 PASS" severity note;
    finish;
  end process;

end architecture sim;
