-- tb_bscane2_bridge.vhd — Lane B: GHDL self-consistency proof of the BSCANE2
-- tunnel transport (bscane2_stub -> bscane2_tap_bridge -> jtag_debug_chain).
--
-- A virtual JTAG host frames an inner-TAP IDCODE scan (IR=IDCODE, then a 32-bit
-- DR scan) using the "Simple nested-TAP tunnel v1" framing the bridge decodes:
-- two outer USER-DR bits per inner TCK step (TMS then TDI). If the bridge and
-- the inner TAP are consistent, the tunnelled DR scan reads back the TAP IDCODE
-- 0x15350067 — proving the FPGA-side de-frame + raw-JTAG replay works end to end
-- through the unmodified debug chain.
--
-- SCOPE (evidence honesty): this proves the FPGA-side tunnel logic against a host
-- that frames identically. Bit-exact interop with OpenOCD 0.12's
-- `riscv use_bscan_tunnel` encoding is a separate BOARD bring-up item (Phase 3),
-- filed in doc/08_tracking/bug — see the bscane2_tap_bridge header. Prints
-- "BSCANE2 TUNNEL SELF-CONSISTENT PASS" only if the IDCODE assert holds.

library ieee;
use ieee.std_logic_1164.all;
use std.env.all;

entity tb_bscane2_bridge is
end entity tb_bscane2_bridge;

architecture sim of tb_bscane2_bridge is
  constant CLK_PERIOD : time := 10 ns;
  constant EXPECTED_IDCODE : std_logic_vector(31 downto 0) := x"15350067";

  signal clk    : std_logic := '0';
  signal rst_n  : std_logic := '0';

  -- stub virtual-JTAG host drive
  signal v_sel, v_drck, v_shift, v_capture, v_update, v_tdi : std_logic := '0';

  -- stub <-> bridge
  signal b_sel, b_drck, b_shift, b_capture, b_update, b_tdi, b_tdo : std_logic;

  -- bridge <-> jtag_debug_chain (raw inner JTAG)
  signal tck, tms, tdi, tdo : std_logic;
  signal trst_n : std_logic := '0';

  -- unused chain observation
  signal uart_tx, o_halted, o_running, o_step : std_logic;
  signal o_pc  : std_logic_vector(31 downto 0);
  signal o_reg : std_logic_vector(31 downto 0);
begin
  clk <= not clk after CLK_PERIOD / 2;

  u_stub : entity work.bscane2_stub
    generic map (JTAG_CHAIN => 1)
    port map (
      CAPTURE => b_capture, DRCK => b_drck, RESET => open, RUNTEST => open,
      SEL => b_sel, SHIFT => b_shift, TCK => open, TMS => open,
      UPDATE => b_update, TDI => b_tdi, TDO => b_tdo,
      v_capture => v_capture, v_drck => v_drck, v_sel => v_sel,
      v_shift => v_shift, v_update => v_update, v_tdi => v_tdi);

  u_bridge : entity work.bscane2_tap_bridge
    port map (
      clk => clk, rst_n => rst_n,
      bsc_sel => b_sel, bsc_drck => b_drck, bsc_capture => b_capture,
      bsc_shift => b_shift, bsc_update => b_update, bsc_tdi => b_tdi,
      bsc_tdo => b_tdo,
      tck_o => tck, tms_o => tms, tdi_o => tdi, tdo_i => tdo);

  u_chain : entity work.jtag_debug_chain
    generic map (IDCODE_VALUE => EXPECTED_IDCODE)
    port map (
      clk => clk, rst_n => rst_n,
      tck => tck, tms => tms, tdi => tdi, trst_n => trst_n, tdo => tdo,
      uart_tx => uart_tx,
      o_halted => o_halted, o_running => o_running, o_step => o_step,
      o_dbg_pc_full => o_pc, o_dbg_reg_data => o_reg);

  stim : process
    -- Shift one outer USER-DR bit through the stub (SEL & SHIFT already high).
    procedure outer_bit(b : std_logic) is
    begin
      v_tdi <= b;
      wait for 40 ns;      -- setup + let the clk-domain sync see DRCK low
      v_drck <= '1';
      wait for 60 ns;      -- DRCK high: 3-FF sync catches a clean rising edge
      v_drck <= '0';
      wait for 60 ns;      -- DRCK low tail
    end procedure;

    -- One inner-TAP TCK step, tunnelled as TMS bit then TDI bit. After the pair
    -- the bridge has pulsed the inner TCK and captured the inner TDO; give it
    -- time to settle before the next step.
    procedure inner_step(tms_v : std_logic; tdi_v : std_logic) is
    begin
      outer_bit(tms_v);
      outer_bit(tdi_v);
      wait for 120 ns;     -- inner TCK pulse + TDO capture settle
    end procedure;

    variable idc : std_logic_vector(31 downto 0) := (others => '0');
  begin
    -- Reset both domains.
    trst_n <= '0'; rst_n <= '0';
    wait for 200 ns;
    trst_n <= '1'; rst_n <= '1';
    wait for 200 ns;

    -- Enter a USER-DR shift session (SEL & SHIFT held for the whole navigation;
    -- a CAPTURE strobe aligns the bridge's pair phase).
    v_sel <= '1';
    v_capture <= '1'; wait for 100 ns; v_capture <= '0';
    v_shift <= '1';

    -- Drive the inner TAP: guarantee Test-Logic-Reset, then IDCODE IR + DR scan.
    for k in 1 to 6 loop inner_step('1', '0'); end loop;  -- -> TLR
    inner_step('0', '0');                                  -- TLR -> RTI
    -- IR scan = IDCODE ("00001", LSB first): RTI->SelDR->SelIR->CapIR->ShiftIR
    inner_step('1', '0');   -- RTI -> Select-DR
    inner_step('1', '0');   -- Select-DR -> Select-IR
    inner_step('0', '0');   -- Select-IR -> Capture-IR
    inner_step('0', '0');   -- Capture-IR -> Shift-IR
    inner_step('0', '1');   -- IR bit0 = 1
    inner_step('0', '0');   -- IR bit1 = 0
    inner_step('0', '0');   -- IR bit2 = 0
    inner_step('0', '0');   -- IR bit3 = 0
    inner_step('1', '0');   -- IR bit4 = 0, exit
    inner_step('1', '0');   -- Exit1-IR -> Update-IR
    inner_step('0', '0');   -- Update-IR -> RTI
    -- DR scan (32 bits): RTI->SelDR->CapDR->ShiftDR, read TDO at each step top.
    inner_step('1', '0');   -- RTI -> Select-DR
    inner_step('0', '0');   -- Select-DR -> Capture-DR
    inner_step('0', '0');   -- Capture-DR -> Shift-DR (LSB now in tdo_cap)
    for i in 0 to 31 loop
      idc(i) := b_tdo;                        -- captured bit i (JTAG read timing)
      if i = 31 then inner_step('1', '0'); else inner_step('0', '0'); end if;
    end loop;

    assert idc = EXPECTED_IDCODE
      report "BSCANE2 TUNNEL FAIL: IDCODE readback 0x" & to_hstring(idc)
             & " /= 0x" & to_hstring(EXPECTED_IDCODE) severity failure;
    report "BSCANE2 TUNNEL SELF-CONSISTENT PASS: IDCODE 0x" & to_hstring(idc)
           & " round-tripped through the tunnel + bridge + inner TAP"
      severity note;
    finish;
  end process;

end architecture sim;
