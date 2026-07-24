-- bscane2_tap_bridge.vhd — Lane B: Xilinx BSCANE2 tunnel -> raw JTAG adapter.
--
-- PURPOSE: reach the Simple RISC-V debug TAP (jtag_tap in jtag_debug_chain)
-- through the SAME FT4232H/USB JTAG chain used to PROGRAM the KV260 — zero extra
-- cabling — by tunnelling the inner TAP inside a Xilinx USER JTAG instruction via
-- the BSCANE2 primitive. OpenOCD reaches it with `riscv use_bscan_tunnel`.
--
-- WHAT THIS UNIT DOES: the BSCANE2 primitive (instantiated in soc_top_rv32.vhd,
-- USER<n> instruction) hands us the standard BSCAN data-register strobes —
-- SEL/SHIFT/CAPTURE/UPDATE/TDI/TDO clocked by DRCK. This bridge de-frames the
-- tunnelled bitstream and REPLAYS it as a raw {tck,tms,tdi}/tdo JTAG sequence
-- driving the unmodified jtag_debug_chain inner TAP, so the whole landed +
-- verified debug back-end (TAP -> DTM -> CDC -> DM -> rv32 hart) is reused as-is.
--
-- TUNNEL FRAMING ("Simple nested-TAP tunnel v1"): while SEL & SHIFT, the outer
-- USER-DR bitstream is a sequence of inner-TAP steps, TWO outer bits per inner
-- TCK: the first bit of a pair = inner TMS, the second = inner TDI. For each
-- completed pair the bridge drives tms_o/tdi_o and issues ONE inner TCK pulse
-- (inner TCK is a clk-gated pulse — the inner TAP + DTM run in the core-clk
-- domain and jtag_debug_chain already crosses to it), then shifts the inner TDO
-- back onto BSCANE2 TDO. This lets OpenOCD walk the inner TAP through full IR and
-- DR scans (IDCODE / DTMCS / DMI) inside one USER instruction.
--
-- *** BOARD-VERIFY ITEM (Phase 3) ***: the v1 framing above is the FPGA-side
-- contract this bridge implements and is proven self-consistent in
-- tb_bscane2_bridge (a host model that frames identically drives IDCODE/DTMCS/DMI
-- through the real jtag_debug_chain). Bit-exact interop with OpenOCD 0.12's
-- `riscv use_bscan_tunnel <irlen> {0|1}` DATA_REGISTER/NESTED_TAP encoding must
-- be confirmed against real silicon (or bridged with a small OpenOCD tcl tunnel
-- shim). Tracked in doc/08_tracking/bug — do NOT claim OpenOCD interop until the
-- board transcript exists. The VERIFIED zero-risk transport meanwhile is raw
-- JTAG on PMOD pins straight into jtag_debug_chain (standard OpenOCD `ftdi`).
--
-- This unit adds NO debug semantics; it is purely a transport de-frame + replay.

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

entity bscane2_tap_bridge is
  port (
    clk    : in  std_logic;   -- core-clk domain (inner TAP/DTM run here)
    rst_n  : in  std_logic;

    -- BSCANE2 data-register interface (from the primitive / a sim stub).
    bsc_sel     : in  std_logic;
    bsc_drck    : in  std_logic;
    bsc_capture : in  std_logic;
    bsc_shift   : in  std_logic;
    bsc_update  : in  std_logic;
    bsc_tdi     : in  std_logic;
    bsc_tdo     : out std_logic;

    -- Reconstructed raw JTAG to the inner TAP (jtag_debug_chain).
    tck_o  : out std_logic;
    tms_o  : out std_logic;
    tdi_o  : out std_logic;
    tdo_i  : in  std_logic
  );
end entity bscane2_tap_bridge;

architecture rtl of bscane2_tap_bridge is
  -- BSCANE2 DRCK synchronized into clk + rising-edge detect (DRCK is slow JTAG).
  signal drck_sync : std_logic_vector(2 downto 0) := (others => '0');
  signal sel_sync  : std_logic_vector(1 downto 0) := (others => '0');
  signal shift_s   : std_logic_vector(1 downto 0) := (others => '0');
  signal tdi_s     : std_logic_vector(1 downto 0) := (others => '0');
  signal drck_rise : std_logic;

  signal phase    : std_logic := '0';               -- 0 = expect TMS bit, 1 = TDI bit
  signal tms_lat  : std_logic := '0';
  signal tms_r    : std_logic := '0';
  signal tdi_r    : std_logic := '0';
  signal inner_tck: std_logic := '0';               -- generated inner TCK level
  signal tck_cnt  : unsigned(2 downto 0) := (others => '0');
  signal step_go  : std_logic := '0';               -- launch one inner TCK pulse
  signal tdo_cap  : std_logic := '0';               -- inner TDO captured for readback
begin
  -- Synchronize the BSCANE2 strobes into the core clk domain.
  sync : process (clk)
  begin
    if rising_edge(clk) then
      if rst_n = '0' then
        drck_sync <= (others => '0');
        sel_sync  <= (others => '0');
        shift_s   <= (others => '0');
        tdi_s     <= (others => '0');
      else
        drck_sync <= drck_sync(1 downto 0) & bsc_drck;
        sel_sync  <= sel_sync(0) & bsc_sel;
        shift_s   <= shift_s(0) & bsc_shift;
        tdi_s     <= tdi_s(0) & bsc_tdi;
      end if;
    end if;
  end process;
  drck_rise <= drck_sync(1) and not drck_sync(2);

  -- Tunnel de-frame: two outer shift bits per inner TCK step (TMS then TDI).
  deframe : process (clk)
  begin
    if rising_edge(clk) then
      if rst_n = '0' then
        phase   <= '0';
        tms_lat <= '0';
        step_go <= '0';
      else
        step_go <= '0';
        if sel_sync(1) = '0' or bsc_capture = '1' then
          phase <= '0';                       -- (re)align at each fresh scan
        elsif drck_rise = '1' and shift_s(1) = '1' then
          if phase = '0' then
            tms_lat <= tdi_s(1);              -- first bit of the pair = inner TMS
            phase   <= '1';
          else
            tms_r   <= tms_lat;              -- second bit = inner TDI: emit step
            tdi_r   <= tdi_s(1);
            step_go <= '1';
            phase   <= '0';
          end if;
        end if;
      end if;
    end if;
  end process;

  -- Inner TCK generator: on step_go, emit one clean HIGH/LOW inner TCK pulse
  -- (a few core-clk cycles wide) so the inner TAP registers one JTAG edge and
  -- updates its TDO on the falling inner edge.
  tckgen : process (clk)
  begin
    if rising_edge(clk) then
      if rst_n = '0' then
        inner_tck <= '0';
        tck_cnt   <= (others => '0');
        tdo_cap   <= '0';
      elsif step_go = '1' then
        inner_tck <= '1';
        tck_cnt   <= "100";                  -- inner TCK high for 2 clks
      elsif tck_cnt /= "000" then
        tck_cnt <= tck_cnt - 1;
        if tck_cnt = "010" then
          inner_tck <= '0';                  -- falling edge of inner TCK
        elsif tck_cnt = "001" then
          tdo_cap <= tdo_i;                  -- one clk AFTER the fall: TDO settled
        end if;
      end if;
    end if;
  end process;

  tck_o   <= inner_tck;
  tms_o   <= tms_r;
  tdi_o   <= tdi_r;
  bsc_tdo <= tdo_cap;

end architecture rtl;
