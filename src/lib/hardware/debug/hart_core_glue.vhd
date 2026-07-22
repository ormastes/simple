-- hart_core_glue.vhd — Lane EE: real rv32 hart behind the Debug Module.
--
-- Integrates the REAL rv32_exec_core (examples/09_embedded/fpga_riscv/rtl,
-- READ-ONLY, instantiated not edited) behind the landed riscv_debug_module so
-- that halt / resume / single-step / abstract-command GPR readback act on a
-- genuinely executing hart rather than the fake-hart model the Stage-1..5
-- testbenches used.
--
-- HALT MECHANISM (wrapper level; core has NO halt/clock-enable/fetch port —
-- its entity is only clk/rst + debug_* observation outputs):
--   The core is CLOCK-GATED. `core_run` gates the core's clock; when the DM
--   asserts haltreq the wrapper drops core_run so the core's clock stops and
--   the hart freezes in place (pc_q/regs_q hold). resume re-enables the clock.
--   The enable is latched on the FALLING edge of clk so the gated clock only
--   ever delivers whole pulses (no runt clock on a mid-cycle enable change).
--   On real silicon this maps to a clock-enable / BUFGCE (the core has no CE
--   port) — a board-bring-up note, not a functional change.
--
-- GPR READBACK is bridged from the core's real committed registers.  Lane KK
-- added ADDITIVE dbg_reg_addr/dbg_reg_data/dbg_pc ports to rv32_exec_core, so
-- abstract-command GPR reads now return the FULL 32-bit committed value of any
-- x0..x31 (dbg_reg_addr is driven by the DM's gpr_regno; the core is
-- clock-gated during readback so the combinational tap is stable) and the DM's
-- pc_i/dpc is fed by the full-width pc.  SBA-into-instruction-fetch still needs
-- the ROM to be writable RAM (the core fetches from internal ROM); see
-- doc/08_tracking/bug/ for that remaining core-gap request.
--
-- SBA master is wired to a wrapper-owned sba_test_mem so the DM's system-bus
-- path is exercised through the glue; the core fetches from its OWN internal
-- ROM (rv32_payload.mem), so this SBA memory is NOT the core's instruction
-- source (documented limitation).

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

entity hart_core_glue is
  port (
    clk   : in  std_logic;
    rst_n : in  std_logic;

    -- DMI slave (drive through dmi_bus, exactly like the Stage tbs drive the DM)
    dmi_valid : in  std_logic;
    dmi_addr  : in  std_logic_vector(6 downto 0);
    dmi_wdata : in  std_logic_vector(31 downto 0);
    dmi_op    : in  std_logic_vector(1 downto 0);
    dmi_rdata : out std_logic_vector(31 downto 0);
    dmi_resp  : out std_logic_vector(1 downto 0);
    dmi_ready : out std_logic;

    -- Observation (for the testbench asserts / waveforms)
    o_halted    : out std_logic;
    o_running   : out std_logic;
    o_step      : out std_logic;
    o_core_run  : out std_logic;
    o_debug_pc  : out std_logic_vector(15 downto 0);
    o_debug_a0  : out std_logic_vector(7 downto 0);
    o_debug_ra  : out std_logic_vector(15 downto 0);
    o_debug_sp  : out std_logic_vector(15 downto 0);
    -- Lane KK: full-width PC + full-regfile readback observation taps
    o_dbg_pc_full   : out std_logic_vector(31 downto 0);
    o_dbg_reg_data  : out std_logic_vector(31 downto 0)
  );
end entity hart_core_glue;

architecture rtl of hart_core_glue is
  -- DM <-> hart glue signals
  signal haltreq_s   : std_logic;
  signal resumereq_s : std_logic;
  signal ndmreset_s  : std_logic;
  signal halted_s    : std_logic;
  signal running_s   : std_logic;

  signal gpr_re_s    : std_logic;
  signal gpr_we_s    : std_logic;
  signal gpr_regno_s : std_logic_vector(4 downto 0);
  signal gpr_wdata_s : std_logic_vector(63 downto 0);
  signal gpr_rdata_s : std_logic_vector(63 downto 0) := (others => '0');
  signal gpr_ack_s   : std_logic := '0';

  signal pc_i_s      : std_logic_vector(63 downto 0);
  signal dpc_o_s     : std_logic_vector(63 downto 0);
  signal step_o_s    : std_logic;

  -- SBA master <-> wrapper-owned exec memory
  signal sb_re_s    : std_logic;
  signal sb_we_s    : std_logic;
  signal sb_addr_s  : std_logic_vector(63 downto 0);
  signal sb_wdata_s : std_logic_vector(63 downto 0);
  signal sb_size_s  : std_logic_vector(1 downto 0);
  signal sb_rdata_s : std_logic_vector(63 downto 0);
  signal sb_ack_s   : std_logic;
  signal sb_err_s   : std_logic;

  -- Core clock gating + control FSM
  signal core_run       : std_logic := '0';  -- 1 => core clock enabled
  signal core_run_lat   : std_logic := '0';  -- falling-edge latched enable
  signal halted_r       : std_logic := '1';  -- start halted (awaiting resume)
  signal step_pending   : std_logic := '0';
  signal step_pc_prev   : std_logic_vector(31 downto 0) := (others => '0');
  signal resumereq_d    : std_logic := '0';
  signal core_rst       : std_logic;
  signal core_clk_en    : std_logic;
  signal core_clk       : std_logic;

  -- Core debug outputs
  signal c_uart_tx    : std_logic;
  signal c_dbg_valid  : std_logic;
  signal c_dbg_byte   : std_logic_vector(7 downto 0);
  signal c_dbg_pc     : std_logic_vector(15 downto 0);
  signal c_dbg_ins    : std_logic_vector(31 downto 0);
  signal c_dbg_a0     : std_logic_vector(7 downto 0);
  signal c_dbg_ra     : std_logic_vector(15 downto 0);
  signal c_dbg_sp     : std_logic_vector(15 downto 0);
  signal c_dbg_phase  : std_logic_vector(3 downto 0);
  -- Lane KK: full-regfile + full-pc debug taps from the core
  signal c_dbg_reg_data : std_logic_vector(31 downto 0);
  signal c_dbg_pc_full  : std_logic_vector(31 downto 0);
begin
  ----------------------------------------------------------------------------
  -- Debug Module (landed, unmodified)
  ----------------------------------------------------------------------------
  u_dm : entity work.riscv_debug_module
    port map (
      clk => clk, rst_n => rst_n,
      dmi_valid => dmi_valid, dmi_addr => dmi_addr,
      dmi_wdata => dmi_wdata, dmi_op => dmi_op,
      dmi_rdata => dmi_rdata, dmi_resp => dmi_resp, dmi_ready => dmi_ready,
      haltreq_o => haltreq_s, resumereq_o => resumereq_s,
      ndmreset_o => ndmreset_s,
      halted_i => halted_s, running_i => running_s,
      gpr_re_o => gpr_re_s, gpr_we_o => gpr_we_s,
      gpr_regno_o => gpr_regno_s, gpr_wdata_o => gpr_wdata_s,
      gpr_rdata_i => gpr_rdata_s, gpr_ack_i => gpr_ack_s,
      pc_i => pc_i_s, prv_i => "11", ebreak_i => '0',
      dpc_o => dpc_o_s, step_o => step_o_s,
      sb_re_o => sb_re_s, sb_we_o => sb_we_s,
      sb_addr_o => sb_addr_s, sb_wdata_o => sb_wdata_s, sb_size_o => sb_size_s,
      sb_rdata_i => sb_rdata_s, sb_ack_i => sb_ack_s, sb_err_i => sb_err_s);

  ----------------------------------------------------------------------------
  -- Real rv32 hart (READ-ONLY core, clock-gated)
  ----------------------------------------------------------------------------
  core_rst    <= (not rst_n) or ndmreset_s;
  -- Run the clock while executing OR while resetting (so the core's own
  -- synchronous reset can initialize even from a halted start).
  core_clk_en <= core_run or core_rst;

  -- Falling-edge enable latch => the gated clock only emits whole pulses.
  enable_latch : process (clk)
  begin
    if falling_edge(clk) then
      core_run_lat <= core_clk_en;
    end if;
  end process;
  core_clk <= clk and core_run_lat;

  u_core : entity work.rv32_exec_core
    port map (
      clk => core_clk, rst => core_rst, uart_tx => c_uart_tx,
      debug_uart_valid => c_dbg_valid, debug_uart_byte => c_dbg_byte,
      debug_pc => c_dbg_pc, debug_ins => c_dbg_ins, debug_a0 => c_dbg_a0,
      debug_ra => c_dbg_ra, debug_sp => c_dbg_sp, debug_phase => c_dbg_phase,
      -- Lane KK: additive debug ports — DM regno selects the register; full
      -- committed value and full pc come straight back out combinationally.
      dbg_reg_addr => gpr_regno_s,
      dbg_reg_data => c_dbg_reg_data,
      dbg_pc => c_dbg_pc_full);

  ----------------------------------------------------------------------------
  -- Wrapper-owned SBA exec memory (DM system-bus path exercise)
  ----------------------------------------------------------------------------
  u_sbamem : entity work.sba_test_mem
    port map (
      clk => clk, rst_n => rst_n,
      sb_re_i => sb_re_s, sb_we_i => sb_we_s,
      sb_addr_i => sb_addr_s, sb_wdata_i => sb_wdata_s, sb_size_i => sb_size_s,
      sb_rdata_o => sb_rdata_s, sb_ack_o => sb_ack_s, sb_err_o => sb_err_s);

  ----------------------------------------------------------------------------
  -- Halt / resume / single-step control (runs on the ungated clk)
  ----------------------------------------------------------------------------
  ctrl : process (clk)
  begin
    if rising_edge(clk) then
      if rst_n = '0' then
        core_run     <= '0';
        halted_r     <= '1';   -- start halted; tb issues resume to run
        step_pending <= '0';
        resumereq_d  <= '0';
      else
        resumereq_d <= resumereq_s;
        if halted_r = '0' then
          -- Running: single-step auto-halt after exactly one retire, else honor
          -- the DM level haltreq.
          if step_pending = '1' then
            if c_dbg_pc_full /= step_pc_prev then
              core_run     <= '0';
              halted_r     <= '1';
              step_pending <= '0';
            end if;
          elsif haltreq_s = '1' then
            core_run <= '0';
            halted_r <= '1';
          end if;
        else
          -- Halted: on a resumereq rising edge, run (one insn if step_o set).
          if resumereq_s = '1' and resumereq_d = '0' then
            core_run <= '1';
            halted_r <= '0';
            if step_o_s = '1' then
              step_pending <= '1';
              step_pc_prev <= c_dbg_pc_full;
            else
              step_pending <= '0';
            end if;
          end if;
        end if;
      end if;
    end if;
  end process;

  halted_s  <= halted_r;
  running_s <= not halted_r;
  pc_i_s    <= x"00000000" & c_dbg_pc_full;  -- Lane KK: real full-width pc into dpc

  ----------------------------------------------------------------------------
  -- Abstract-command GPR readback bridge (real committed registers).
  -- Core exposes x1(ra)/x2(sp)/x10(a0) + pc only; other regnos return 0.
  -- Handshake mirrors the proven Stage-3 fake-hart model: gpr_re/we are held
  -- (level) by the DM until we pulse gpr_ack for one clock; we answer after a
  -- 2-cycle latency and capture rdata synchronously at ack.  The core is
  -- clock-gated (halted) during any readback, so c_dbg_* are stable.
  ----------------------------------------------------------------------------
  gpr_bridge : process (clk)
    variable cnt : natural := 0;
  begin
    if rising_edge(clk) then
      if rst_n = '0' then
        gpr_ack_s   <= '0';
        gpr_rdata_s <= (others => '0');
        cnt := 0;
      else
        gpr_ack_s <= '0';
        if (gpr_re_s = '1' or gpr_we_s = '1') and gpr_ack_s = '0' then
          if cnt = 2 then
            cnt := 0;
            gpr_ack_s <= '1';
            if gpr_re_s = '1' then
              -- Lane KK: FULL x0..x31 readback.  dbg_reg_addr is driven by
              -- gpr_regno_s, so c_dbg_reg_data already holds the requested
              -- register's full 32-bit committed value (core clock-gated =>
              -- stable).  rv32 => upper 32 bits of the 64-bit DM word are 0.
              gpr_rdata_s <= x"00000000" & c_dbg_reg_data;
            end if;
            -- GPR writes are accepted (ack) but not written back: the core
            -- exposes no register write port (read-only debug observation).
          else
            cnt := cnt + 1;
          end if;
        else
          cnt := 0;
        end if;
      end if;
    end if;
  end process;

  -- Observation
  o_halted   <= halted_r;
  o_running  <= not halted_r;
  o_step     <= step_o_s;
  o_core_run <= core_run;
  o_debug_pc <= c_dbg_pc;
  o_debug_a0 <= c_dbg_a0;
  o_debug_ra <= c_dbg_ra;
  o_debug_sp <= c_dbg_sp;
  o_dbg_pc_full  <= c_dbg_pc_full;
  o_dbg_reg_data <= c_dbg_reg_data;
end architecture rtl;
