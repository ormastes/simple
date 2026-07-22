-- riscv_debug_module.vhd — RISC-V Debug Spec v0.13 Debug Module (Stage 3).
--
-- Top-level DM: instantiates debug_registers (DMI-visible register block)
-- and implements the halt/resume handshake state machine toward the hart.
-- Stage 3 adds abstract register access (DATA0/DATA1, COMMAND access-
-- register, ABSTRACTCS busy/cmderr) with a stub-level GPR port toward the
-- hart; the abstract-command engine itself lives in debug_registers.
-- Stage 4 adds DM-resident debug CSRs dpc (0x7B1) / dcsr (0x7B0) with
-- stub-level hart ports (pc_i/prv_i/ebreak_i in, dpc_o/step_o out).
--
-- Hart-side integration is DEFERRED (Stage 2 scope): only stub ports are
-- exposed — haltreq_o / resumereq_o / ndmreset_o outputs, halted_i /
-- running_i status inputs. The testbench models a fake hart.
--
-- Behavior:
--   * haltreq_o   = DMCONTROL.haltreq (level) while the hart is not halted
--                   and the DM is active. Deasserts once halted_i = '1'.
--   * resumereq_o = asserted from a DMCONTROL.resumereq=1 write until the
--                   hart reports running_i = '1'; then resumeack is set.
--                   resumeack clears on the next resumereq write.
--   * ndmreset_o  = DMCONTROL.ndmreset (level). havereset bookkeeping is in
--                   debug_registers (set on ndmreset 0->1 write, cleared by
--                   ackhavereset).
--   * dmactive=0 clears all handshake state.
--
-- Single-hart DM: hartsel is ignored (reads as zero); documented in
-- debug_registers.vhd.

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

entity riscv_debug_module is
  port (
    clk   : in  std_logic;
    rst_n : in  std_logic;

    -- DMI slave (forwarded 0x10..0x1F requests from dmi_bus dm_* port)
    dmi_valid : in  std_logic;
    dmi_addr  : in  std_logic_vector(6 downto 0);
    dmi_wdata : in  std_logic_vector(31 downto 0);
    dmi_op    : in  std_logic_vector(1 downto 0);
    dmi_rdata : out std_logic_vector(31 downto 0);
    dmi_resp  : out std_logic_vector(1 downto 0);
    dmi_ready : out std_logic;

    -- Hart-side stub ports (integration deferred to a later stage)
    haltreq_o   : out std_logic;
    resumereq_o : out std_logic;
    ndmreset_o  : out std_logic;
    halted_i    : in  std_logic;
    running_i   : in  std_logic;

    -- Abstract-command GPR port (Stage 3; stub-level, matches the deferred
    -- hart integration): re/we held with regno/wdata until ack_i pulses.
    -- Defaults let pre-Stage-3 instantiations leave these unconnected.
    gpr_re_o    : out std_logic;
    gpr_we_o    : out std_logic;
    gpr_regno_o : out std_logic_vector(4 downto 0);
    gpr_wdata_o : out std_logic_vector(63 downto 0);
    gpr_rdata_i : in  std_logic_vector(63 downto 0) := (others => '0');
    gpr_ack_i   : in  std_logic := '0';

    -- Stage-4 debug-CSR hart stub ports (dpc/dcsr live in the DM): pc_i is
    -- captured into dpc on halt, dpc_o is the resume address, prv_i is
    -- captured into dcsr.prv on halt, ebreak_i marks an ebreak-caused halt
    -- (dcsr.cause=1), step_o exports dcsr.step for single-step modeling.
    -- Defaults let pre-Stage-4 instantiations leave these unconnected.
    pc_i     : in  std_logic_vector(63 downto 0) := (others => '0');
    prv_i    : in  std_logic_vector(1 downto 0)  := "11";
    ebreak_i : in  std_logic := '0';
    dpc_o    : out std_logic_vector(63 downto 0);
    step_o   : out std_logic
  );
end entity riscv_debug_module;

architecture rtl of riscv_debug_module is

  signal dmactive_s     : std_logic;
  signal ndmreset_s     : std_logic;
  signal haltreq_lvl_s  : std_logic;
  signal resume_pulse_s : std_logic;

  signal resume_pending_r : std_logic := '0';
  signal resumeack_r      : std_logic := '0';

begin

  u_regs : entity work.debug_registers
    port map (
      clk   => clk,
      rst_n => rst_n,

      dmi_valid => dmi_valid,
      dmi_addr  => dmi_addr,
      dmi_wdata => dmi_wdata,
      dmi_op    => dmi_op,
      dmi_rdata => dmi_rdata,
      dmi_resp  => dmi_resp,
      dmi_ready => dmi_ready,

      dmactive_o        => dmactive_s,
      ndmreset_o        => ndmreset_s,
      haltreq_o         => haltreq_lvl_s,
      resumereq_pulse_o => resume_pulse_s,

      gpr_re_o    => gpr_re_o,
      gpr_we_o    => gpr_we_o,
      gpr_regno_o => gpr_regno_o,
      gpr_wdata_o => gpr_wdata_o,
      gpr_rdata_i => gpr_rdata_i,
      gpr_ack_i   => gpr_ack_i,

      pc_i     => pc_i,
      prv_i    => prv_i,
      ebreak_i => ebreak_i,
      dpc_o    => dpc_o,
      step_o   => step_o,

      halted_i    => halted_i,
      running_i   => running_i,
      resumeack_i => resumeack_r);

  -- Resume handshake: request -> wait for running -> ack.
  process (clk, rst_n)
  begin
    if rst_n = '0' then
      resume_pending_r <= '0';
      resumeack_r      <= '0';
    elsif rising_edge(clk) then
      if dmactive_s = '0' then
        resume_pending_r <= '0';
        resumeack_r      <= '0';
      else
        if resume_pulse_s = '1' then
          resume_pending_r <= '1';
          resumeack_r      <= '0';  -- resumeack clears on resumereq write
        elsif resume_pending_r = '1' and running_i = '1' then
          resume_pending_r <= '0';
          resumeack_r      <= '1';
        end if;
      end if;
    end if;
  end process;

  haltreq_o   <= haltreq_lvl_s and (not halted_i) and dmactive_s;
  resumereq_o <= resume_pending_r and dmactive_s;
  ndmreset_o  <= ndmreset_s;

end architecture rtl;
