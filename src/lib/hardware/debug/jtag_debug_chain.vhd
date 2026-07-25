-- jtag_debug_chain.vhd — Lane B: board-ready JTAG debug back-end bundle.
--
-- One reusable structural unit that wires the landed Simple RISC-V debug stack
-- into a single hart-debug seam so a SoC (or a testbench) can drop it in behind
-- one entity:
--
--   raw JTAG  ->  jtag_tap  ->  riscv_dtm  ==CDC==>  dmi_bus  ->  hart_core_glue
--   (tck dom)     (tck dom)     (tck dom)   tck→clk   (clk dom)   (clk dom: DM +
--                                                                  real rv32 hart)
--
-- WHY A CDC: the JTAG TAP + DTM are genuinely in the JTAG TCK clock domain (on
-- silicon TCK comes from the debug probe / BSCANE2 DRCK — a real, slow, async
-- clock), while the Debug Module, the clock-gated rv32 hart and its control FSM
-- run in the fast core clock domain (`clk`, 25 MHz on the KV260 rv32 SoC). The
-- landed Stage tbs sidestepped this by running everything on one clock; a real
-- board cannot. This bundle adds the missing, standard req/ack CDC between the
-- DTM's single-tck-cycle DMI request pulse and the clk-domain dmi_bus, and a
-- level handshake back for the completion — so the same RTL is correct whether
-- tck is faster, slower, or unrelated to clk.
--
-- TRANSPORT: the raw tck/tms/tdi/tdo pins are the transport seam. They are fed
-- either by external PMOD JTAG pins (FT2232H, standard OpenOCD `ftdi`) or by a
-- Xilinx BSCANE2 tunnel bridge (bscane2_tap_bridge) — see soc_top_rv32.vhd.
--
-- The DM abstract-command / SBA / halt / step behaviour is exactly the landed,
-- Stage-1..5 + hart-integration verified behaviour; this unit adds no debug
-- semantics, only the clock-domain plumbing and pin fan-out.

library ieee;
use ieee.std_logic_1164.all;

entity jtag_debug_chain is
  generic (
    IDCODE_VALUE : std_logic_vector(31 downto 0) := x"15350067"
  );
  port (
    clk    : in  std_logic;  -- core / DM clock domain
    rst_n  : in  std_logic;  -- active-low system reset (clk domain)

    -- Raw JTAG (TCK clock domain) — from PMOD pins or a BSCANE2 bridge.
    tck    : in  std_logic;
    tms    : in  std_logic;
    tdi    : in  std_logic;
    trst_n : in  std_logic;
    tdo    : out std_logic;

    -- Wrapped-hart UART (soak-loop markers stay visible while debugging).
    uart_tx : out std_logic;

    -- Observation taps (waveforms / tb asserts).
    o_halted       : out std_logic;
    o_running      : out std_logic;
    o_step         : out std_logic;
    o_dbg_pc_full  : out std_logic_vector(31 downto 0);
    o_dbg_reg_data : out std_logic_vector(31 downto 0)
  );
end entity jtag_debug_chain;

architecture rtl of jtag_debug_chain is
  -- TAP <-> DTM external-DR interface
  signal tlr        : std_logic;
  signal sel_dtmcs  : std_logic;
  signal sel_dmi    : std_logic;
  signal capture_en : std_logic;
  signal shift_en   : std_logic;
  signal update_en  : std_logic;
  signal dr_tdi     : std_logic;
  signal dtmcs_tdo  : std_logic;
  signal dmi_tdo    : std_logic;

  -- DTM DMI master (TCK domain)
  signal t_dmi_valid : std_logic;
  signal t_dmi_addr  : std_logic_vector(6 downto 0);
  signal t_dmi_wdata : std_logic_vector(31 downto 0);
  signal t_dmi_op    : std_logic_vector(1 downto 0);
  signal t_dmi_rdata : std_logic_vector(31 downto 0);
  signal t_dmi_resp  : std_logic_vector(1 downto 0);
  signal t_dmi_ready : std_logic;

  -- dmi_bus slave (CLK domain), after CDC
  signal c_dmi_valid : std_logic;
  signal c_dmi_addr  : std_logic_vector(6 downto 0);
  signal c_dmi_wdata : std_logic_vector(31 downto 0);
  signal c_dmi_op    : std_logic_vector(1 downto 0);
  signal c_dmi_rdata : std_logic_vector(31 downto 0);
  signal c_dmi_resp  : std_logic_vector(1 downto 0);
  signal c_dmi_ready : std_logic;

  -- dmi_bus -> glue (DM slave) forwarding port
  signal dm_valid : std_logic;
  signal dm_addr  : std_logic_vector(6 downto 0);
  signal dm_wdata : std_logic_vector(31 downto 0);
  signal dm_op    : std_logic_vector(1 downto 0);
  signal dm_rdata : std_logic_vector(31 downto 0);
  signal dm_resp  : std_logic_vector(1 downto 0);
  signal dm_ready : std_logic;

  -- CDC state (2-phase / toggle req-ack handshake, single outstanding txn).
  -- req_toggle flips (tck) on each DTM request pulse; ack_toggle flips (clk)
  -- when that request has completed. tck-side readiness is `req==ack`, so the
  -- moment a NEW request is issued (req flips) readiness drops until its own
  -- completion re-aligns the toggles — this is what prevents a stale completion
  -- from the previous transaction being mistaken for the new one's response
  -- (the failure mode a persistent done-level CDC exhibits across clock ratios).
  signal req_toggle : std_logic := '0';                                 -- tck domain
  signal req_sync   : std_logic_vector(2 downto 0) := (others => '0');  -- into clk
  signal req_event  : std_logic;                                        -- clk: new request edge
  signal ack_toggle : std_logic := '0';                                 -- clk domain
  signal ack_sync   : std_logic_vector(2 downto 0) := (others => '0');  -- into tck
  signal ack_edge   : std_logic;                                        -- tck: completion edge
  signal resp_valid : std_logic := '0';                                 -- tck: response pending
  signal done_rdata : std_logic_vector(31 downto 0) := (others => '0');
  signal done_resp  : std_logic_vector(1 downto 0)  := (others => '0');
begin
  ----------------------------------------------------------------------------
  -- TAP FSM (TCK domain)
  ----------------------------------------------------------------------------
  u_tap : entity work.jtag_tap
    generic map (IDCODE_VALUE => IDCODE_VALUE)
    port map (
      tck => tck, tms => tms, tdi => tdi, trst_n => trst_n, tdo => tdo,
      tlr_o => tlr,
      sel_dtmcs => sel_dtmcs, sel_dmi => sel_dmi,
      capture_en => capture_en, shift_en => shift_en, update_en => update_en,
      dr_tdi => dr_tdi, dtmcs_tdo => dtmcs_tdo, dmi_tdo => dmi_tdo);

  ----------------------------------------------------------------------------
  -- DTM (TCK domain): DTMCS/DMI DRs + DMI master
  ----------------------------------------------------------------------------
  u_dtm : entity work.riscv_dtm
    port map (
      tck => tck, trst_n => trst_n,
      tlr => tlr,
      sel_dtmcs => sel_dtmcs, sel_dmi => sel_dmi,
      capture_en => capture_en, shift_en => shift_en, update_en => update_en,
      tdi => dr_tdi, dtmcs_tdo => dtmcs_tdo, dmi_tdo => dmi_tdo,
      dmi_valid => t_dmi_valid, dmi_addr => t_dmi_addr, dmi_wdata => t_dmi_wdata,
      dmi_op => t_dmi_op, dmi_rdata => t_dmi_rdata, dmi_resp => t_dmi_resp,
      dmi_ready => t_dmi_ready);

  ----------------------------------------------------------------------------
  -- CDC request side: TCK request pulse -> toggle -> synchronize into CLK ->
  -- one-cycle request event. addr/wdata/op are held stable by the DTM for the
  -- whole busy window, so they are sampled combinationally with the event (only
  -- the control toggle needs metastability-safe synchronization).
  ----------------------------------------------------------------------------
  req_gen : process (tck, trst_n)
  begin
    if trst_n = '0' then
      req_toggle <= '0';
    elsif rising_edge(tck) then
      if t_dmi_valid = '1' then
        req_toggle <= not req_toggle;   -- one flip per DMI request
      end if;
    end if;
  end process;

  req_cdc : process (clk)
  begin
    if rising_edge(clk) then
      if rst_n = '0' then
        req_sync <= (others => '0');
      else
        req_sync <= req_sync(1 downto 0) & req_toggle;
      end if;
    end if;
  end process;
  req_event   <= req_sync(2) xor req_sync(1);   -- either edge = a new request
  c_dmi_valid <= req_event;
  c_dmi_addr  <= t_dmi_addr;                     -- stable during DTM busy window
  c_dmi_wdata <= t_dmi_wdata;
  c_dmi_op    <= t_dmi_op;

  ----------------------------------------------------------------------------
  -- CLK-domain DMI fabric + Debug Module + real rv32 hart.
  ----------------------------------------------------------------------------
  u_dmi : entity work.dmi_bus
    port map (
      clk => clk, rst_n => rst_n,
      valid => c_dmi_valid, addr => c_dmi_addr, wdata => c_dmi_wdata, op => c_dmi_op,
      rdata => c_dmi_rdata, resp => c_dmi_resp, ready => c_dmi_ready,
      dm_valid => dm_valid, dm_addr => dm_addr, dm_wdata => dm_wdata, dm_op => dm_op,
      dm_rdata => dm_rdata, dm_resp => dm_resp, dm_ready => dm_ready);

  u_glue : entity work.hart_core_glue
    port map (
      clk => clk, rst_n => rst_n,
      dmi_valid => dm_valid, dmi_addr => dm_addr,
      dmi_wdata => dm_wdata, dmi_op => dm_op,
      dmi_rdata => dm_rdata, dmi_resp => dm_resp, dmi_ready => dm_ready,
      o_halted => o_halted, o_running => o_running, o_step => o_step,
      o_core_run => open,
      o_debug_pc => open, o_debug_a0 => open, o_debug_ra => open, o_debug_sp => open,
      o_dbg_pc_full => o_dbg_pc_full, o_dbg_reg_data => o_dbg_reg_data,
      o_uart_tx => uart_tx);

  ----------------------------------------------------------------------------
  -- CDC completion side: dmi_bus asserts c_dmi_ready for one CLK cycle when the
  -- transaction resolves. Capture rdata/resp and flip ack_toggle. The toggle is
  -- synchronized into TCK and edge-detected into a one-shot `resp_valid` level.
  --
  -- resp_valid is CLEARED at request issue (t_dmi_valid) and SET on the ack
  -- edge, and t_dmi_ready is additionally masked by `not t_dmi_valid`. This is
  -- what defeats the premature-completion hazard: the DTM sets its busy flag on
  -- the Update-DR edge but only exposes valid_r one TCK edge later, on the very
  -- edge it re-evaluates completion — so ready MUST read low on that edge or the
  -- DTM latches the previous transaction's stale data (observed as a one-
  -- transaction read lag). Masking with t_dmi_valid guarantees ready=0 for that
  -- issue edge, and resp_valid stays low until this request's own ack arrives.
  ----------------------------------------------------------------------------
  ack_gen : process (clk)
  begin
    if rising_edge(clk) then
      if rst_n = '0' then
        ack_toggle <= '0';
        done_rdata <= (others => '0');
        done_resp  <= (others => '0');
      elsif c_dmi_ready = '1' then
        done_rdata <= c_dmi_rdata;
        done_resp  <= c_dmi_resp;
        ack_toggle <= not ack_toggle;   -- one flip per completion
      end if;
    end if;
  end process;

  ack_cdc : process (tck, trst_n)
  begin
    if trst_n = '0' then
      ack_sync   <= (others => '0');
      resp_valid <= '0';
    elsif rising_edge(tck) then
      ack_sync <= ack_sync(1 downto 0) & ack_toggle;
      if t_dmi_valid = '1' then
        resp_valid <= '0';              -- new request: no response yet
      elsif ack_edge = '1' then
        resp_valid <= '1';              -- this request's completion arrived
      end if;
    end if;
  end process;
  ack_edge <= ack_sync(2) xor ack_sync(1);

  -- Ready only for a pending response, and never on the DTM's own issue edge.
  t_dmi_ready <= resp_valid and not t_dmi_valid;
  t_dmi_rdata <= done_rdata;   -- stable: single outstanding transaction
  t_dmi_resp  <= done_resp;

end architecture rtl;
