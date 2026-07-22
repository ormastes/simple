-- debug_registers.vhd — RISC-V Debug Spec v0.13 DM register block (Stage 3).
--
-- DMI slave for addresses 0x10..0x1F plus the abstract-data registers
-- 0x04/0x05 (same 1-cycle valid/ready protocol as dmi_bus scratch): request
-- sampled on the clock where dmi_valid = '1', response (rdata/resp/ready)
-- driven the following clock, ready for 1 clock.
--
-- Implemented registers:
--   0x04 DATA0     — abstract command data, low word (r/w).
--   0x05 DATA1     — abstract command data, high word (r/w).
--                    Stage 4: dmi_bus now forwards the abstract-data window
--                    0x04..0x0B here (scratch shrunk to 0x00..0x03), so
--                    DATA0/DATA1 are reachable through the real bus.
--                    0x06..0x0B read 0 / write ignored (datacount=2).
--   0x10 DMCONTROL  — dmactive(0), ndmreset(1), ackhavereset(28, W1),
--                     resumereq(30, W1 pulse), haltreq(31, level).
--                     Single hart: hasel/hartsello/hartselhi ignored, read 0.
--                     haltreq/resumereq/ackhavereset are write-only (read 0)
--                     per spec field access "W".
--   0x11 DMSTATUS   — version=2 (0.13), authenticated=1 (no auth), and
--                     single-hart status: all==any for halted/running/
--                     resumeack/havereset.
--   0x12 HARTINFO   — all zero (nscratch=0, dataaccess=0, datasize=0).
--   0x16 ABSTRACTCS — datacount(3:0)=2, busy(12), cmderr(10:8, W1C);
--                     progbufsize(28:24)=0 (no program buffer).
--   0x17 COMMAND    — cmdtype 0 (access register) only:
--                       aarsize(22:20): 2 = 32-bit, 3 = 64-bit;
--                       transfer(17), write(16), regno(15:0).
--                     Supported regno: 0x1000..0x101F (GPRs x0..x31), and
--                     (Stage 4) CSR space 0x0000..0x0FFF with exactly two
--                     debug CSRs implemented INSIDE the DM:
--                       0x7B0 dcsr (aarsize=2, or — Stage 5, for the real
--                                   riscv-013 driver which reads CSRs at
--                                   XLEN width — aarsize=3: read zero-
--                                   extends into DATA1, write takes DATA0)
--                       0x7B1 dpc  (aarsize=2 or 3; aarsize=2 accesses the
--                                   low 32 bits, write zero-extends)
--                     (Stage 5) examine/halt-critical stub CSRs so OpenOCD's
--                       riscv-013 driver works without a program buffer
--                       (all replaced by real hart CSRs at hart
--                       integration):
--                       0x301 misa    RO constant RV64IMA
--                                     (0x8000000000001101); write -> cmderr=2
--                       0x300 mstatus RW 64-bit stub register (reset 0)
--                       0x7A0 tselect WARL stub: writes accepted+ignored,
--                                     reads 0 (debugger sees 0 triggers)
--                       0x7A1 tdata1  RO 0 (type=0: no trigger at tselect 0);
--                                     write -> cmderr=2
--                     Any other CSR regno -> cmderr=2 (not supported).
--                     dcsr/dpc accesses complete immediately (no busy
--                     window — the registers live in the DM itself).
--                     cmderr encoding (sticky; new COMMAND writes while
--                     cmderr /= 0 are ignored; W1C via ABSTRACTCS):
--                       1 = busy violation: COMMAND/DATA0/DATA1 written
--                           while an abstract command is executing;
--                       2 = not supported: cmdtype /= 0, aarsize not 2/3,
--                           or transfer=1 with regno outside 0x1000..0x101F;
--                       4 = haltresume: command issued while the hart is not
--                           halted (halted_i = '0').
--                     Check order: busy (1) -> not-supported (2) ->
--                     not-halted (4). transfer=0 with an otherwise valid
--                     command is a successful no-op (still requires halted).
--                     aarsize=2 write zero-extends DATA0 into the 64-bit
--                     GPR; aarsize=2 read returns the low 32 bits in DATA0
--                     and leaves DATA1 unchanged. Writes to regno 0x1000
--                     (x0) are accepted by the DM; the hart keeps x0 = 0.
--                     Reads of DATA0/1 while busy return the current values
--                     without setting cmderr (spec allows cmderr=1 here;
--                     scoped to writes in this implementation).
--   other 0x1x      — read 0 / write ignored, resp = success (harmless
--                     unimplemented optional registers: haltsum, hawindow...).
--
-- Stage-5 System Bus Access (v0.13 §3.10), DMI addresses 0x38..0x3D:
--   0x38 SBCS        — sbversion(31:29)=1 RO; sbbusyerror(22) R/W1C;
--                      sbbusy(21) RO; sbreadonaddr(20) RW; sbaccess(19:17)
--                      RW (only 2=32-bit and 3=64-bit supported, reset 2);
--                      sbautoincrement(16) RW; sbreadondata(15) RW;
--                      sberror(14:12) R/W1C; sbasize(11:5)=64 RO;
--                      sbaccess64(3)=1, sbaccess32(2)=1 RO; 128/16/8 = 0.
--                      Control fields (20..15) are only updated while
--                      sbbusy=0 (spec: writing sbcs while sbbusy is
--                      undefined; this implementation drops the field
--                      update, W1C bits are always honored).
--   0x39 SBADDRESS0  — address bits 31:0. Write while sbbusy=1 sets
--                      sbbusyerror and is dropped. Otherwise the write
--                      lands, and if sbreadonaddr=1 (and sberror=0 and
--                      sbbusyerror=0) a bus read is triggered.
--   0x3A SBADDRESS1  — address bits 63:32 (no trigger).
--   0x3B             — reserved (sbaddress2): read 0 / write ignored.
--   0x3C SBDATA0     — data bits 31:0. Read returns sbdata0; if
--                      sbreadondata=1 (and no error) a new bus read is
--                      triggered after the value is returned. Write stores
--                      wdata into sbdata0 and triggers a bus WRITE of
--                      sbaccess size (64-bit writes use SBDATA1 & SBDATA0).
--                      Any SBDATA0 access or SBADDRESS write while
--                      sbbusy=1 sets sbbusyerror and is dropped.
--   0x3D SBDATA1     — data bits 63:32 (no trigger).
--   sberror encoding: 2 = bad address (bus target flagged sb_err_i);
--                     4 = unsupported sbaccess size (not 2/3) at trigger.
--                     W1C via SBCS(14:12). While sberror/=0 or
--                     sbbusyerror=1, no new bus accesses start.
--   sbautoincrement adds (1 << sbaccess) to SBADDRESS after every
--   SUCCESSFUL bus access (reads and writes; not after sb_err_i).
--   Bus master port: sb_re_o/sb_we_o held level with sb_addr_o/sb_wdata_o/
--   sb_size_o stable until the target pulses sb_ack_i for one clock
--   (sb_err_i sampled with the ack) — same handshake as the GPR port.
--   sbbusy covers the whole window. dmactive=0 resets all SBA state.
--
-- Abstract command execution (GPR port): on an accepted transfer command the
-- block asserts gpr_re_o or gpr_we_o (level) with gpr_regno_o/gpr_wdata_o
-- held stable until the hart pulses gpr_ack_i for one clock; busy is set for
-- the whole window. On read-ack, gpr_rdata_i is captured into DATA0 (and
-- DATA1 when aarsize=3).
--
-- Stage-4 debug CSRs (v0.13), DM-resident, hart-stub-level:
--   dcsr (0x7B0): xdebugver(31:28)=4 (RO), ebreakm(15)/ebreaks(13)/
--     ebreaku(12) (RW), cause(8:6) (RO: 1=ebreak, 3=haltreq, 4=step),
--     step(2) (RW), prv(1:0) (RW, WARL — legal values 0/1/3; a write of 2
--     is ignored and the previous value kept). All other bits read 0.
--   dpc (0x7B1): 64-bit. Captured from pc_i on the halted_i rising edge;
--     driven out on dpc_o so the hart resumes at dpc.
--   cause capture on halt (priority): ebreak_i=1 -> 1; else pending
--     DMCONTROL.haltreq -> 3; else a step-resume was in flight -> 4;
--     default 3. prv is captured from prv_i on the same edge.
--   step: dcsr.step is exported on step_o; when a resumereq is written
--     while step=1 the DM arms step_pending, and the hart (stub/tb model)
--     runs one instruction and re-halts, which is then reported cause=4.
--
-- dmactive semantics: writing DMCONTROL with dmactive=0 resets ALL DM state
-- (including DATA0/1, busy, cmderr and any in-flight GPR access). While
-- dmactive=0, DMCONTROL reads back 0 and all other write bits of the
-- activating write are ignored (fields take effect only once dmactive was
-- already 1 on a previous write) — debugger must write dmactive=1 first,
-- then issue requests, matching the spec's "poll until dmactive reads 1".

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

entity debug_registers is
  port (
    clk   : in  std_logic;
    rst_n : in  std_logic;

    -- DMI slave (forwarded 0x10..0x1F requests from dmi_bus; 0x04/0x05 for
    -- direct-DMI integrations — see header note)
    dmi_valid : in  std_logic;
    dmi_addr  : in  std_logic_vector(6 downto 0);
    dmi_wdata : in  std_logic_vector(31 downto 0);
    dmi_op    : in  std_logic_vector(1 downto 0);
    dmi_rdata : out std_logic_vector(31 downto 0);
    dmi_resp  : out std_logic_vector(1 downto 0);
    dmi_ready : out std_logic;

    -- Control outputs to the DM core state machine
    dmactive_o        : out std_logic;
    ndmreset_o        : out std_logic;
    haltreq_o         : out std_logic;  -- level, as written to DMCONTROL.haltreq
    resumereq_pulse_o : out std_logic;  -- 1-clock pulse per resumereq=1 write

    -- Abstract-command GPR port toward the hart (Stage 3; stub-level,
    -- matches the deferred hart integration): re/we held with regno/wdata
    -- until ack_i pulses for one clock.
    gpr_re_o    : out std_logic;
    gpr_we_o    : out std_logic;
    gpr_regno_o : out std_logic_vector(4 downto 0);
    gpr_wdata_o : out std_logic_vector(63 downto 0);
    gpr_rdata_i : in  std_logic_vector(63 downto 0) := (others => '0');
    gpr_ack_i   : in  std_logic := '0';

    -- Stage-4 debug-CSR hart stub ports. Defaults let pre-Stage-4
    -- instantiations leave these unconnected.
    pc_i     : in  std_logic_vector(63 downto 0) := (others => '0');
    prv_i    : in  std_logic_vector(1 downto 0)  := "11";
    ebreak_i : in  std_logic := '0';
    dpc_o    : out std_logic_vector(63 downto 0);
    step_o   : out std_logic;

    -- Stage-5 system-bus master port (SBA). re/we held with addr/wdata/size
    -- until sb_ack_i pulses for one clock; sb_err_i sampled with the ack.
    -- Defaults let pre-Stage-5 instantiations leave these unconnected.
    sb_re_o    : out std_logic;
    sb_we_o    : out std_logic;
    sb_addr_o  : out std_logic_vector(63 downto 0);
    sb_wdata_o : out std_logic_vector(63 downto 0);
    sb_size_o  : out std_logic_vector(1 downto 0);
    sb_rdata_i : in  std_logic_vector(63 downto 0) := (others => '0');
    sb_ack_i   : in  std_logic := '0';
    sb_err_i   : in  std_logic := '0';

    -- Status inputs (from DM core / hart)
    halted_i    : in  std_logic;
    running_i   : in  std_logic;
    resumeack_i : in  std_logic
  );
end entity debug_registers;

architecture rtl of debug_registers is

  constant A_DATA0      : std_logic_vector(6 downto 0) := "0000100";  -- 0x04
  constant A_DATA1      : std_logic_vector(6 downto 0) := "0000101";  -- 0x05
  constant A_DMCONTROL  : std_logic_vector(6 downto 0) := "0010000";  -- 0x10
  constant A_DMSTATUS   : std_logic_vector(6 downto 0) := "0010001";  -- 0x11
  constant A_HARTINFO   : std_logic_vector(6 downto 0) := "0010010";  -- 0x12
  constant A_ABSTRACTCS : std_logic_vector(6 downto 0) := "0010110";  -- 0x16
  constant A_COMMAND    : std_logic_vector(6 downto 0) := "0010111";  -- 0x17
  constant A_SBCS       : std_logic_vector(6 downto 0) := "0111000";  -- 0x38
  constant A_SBADDRESS0 : std_logic_vector(6 downto 0) := "0111001";  -- 0x39
  constant A_SBADDRESS1 : std_logic_vector(6 downto 0) := "0111010";  -- 0x3A
  constant A_SBDATA0    : std_logic_vector(6 downto 0) := "0111100";  -- 0x3C
  constant A_SBDATA1    : std_logic_vector(6 downto 0) := "0111101";  -- 0x3D

  -- Stage-5 examine-critical stub CSR: misa = RV64 (MXL=2) + I + M + A.
  constant MISA_VALUE : std_logic_vector(63 downto 0) := x"8000000000001101";

  -- Stage-5 stub CSR state (hart integration replaces this with the real
  -- hart CSR file).
  signal mstatus_r : std_logic_vector(63 downto 0) := (others => '0');

  signal dmactive_r  : std_logic := '0';
  signal ndmreset_r  : std_logic := '0';
  signal haltreq_r   : std_logic := '0';
  signal havereset_r : std_logic := '0';
  signal cmderr_r    : std_logic_vector(2 downto 0) := "000";

  signal resume_pulse_r : std_logic := '0';

  -- Abstract command state (Stage 3)
  signal data0_r       : std_logic_vector(31 downto 0) := (others => '0');
  signal data1_r       : std_logic_vector(31 downto 0) := (others => '0');
  signal abusy_r       : std_logic := '0';
  signal exec_write_r  : std_logic := '0';
  signal exec_size64_r : std_logic := '0';
  signal gpr_re_r      : std_logic := '0';
  signal gpr_we_r      : std_logic := '0';
  signal gpr_regno_r   : std_logic_vector(4 downto 0) := (others => '0');
  signal gpr_wdata_r   : std_logic_vector(63 downto 0) := (others => '0');

  -- Stage-4 debug CSR state
  signal dpc_r          : std_logic_vector(63 downto 0) := (others => '0');
  signal dcsr_ebreakm_r : std_logic := '0';
  signal dcsr_ebreaks_r : std_logic := '0';
  signal dcsr_ebreaku_r : std_logic := '0';
  signal dcsr_step_r    : std_logic := '0';
  signal dcsr_cause_r   : std_logic_vector(2 downto 0) := "000";
  signal dcsr_prv_r     : std_logic_vector(1 downto 0) := "11";
  signal step_pending_r : std_logic := '0';
  signal halted_q       : std_logic := '0';

  -- Stage-5 SBA state
  signal sbaddr_r      : std_logic_vector(63 downto 0) := (others => '0');
  signal sbdata_r      : std_logic_vector(63 downto 0) := (others => '0');
  signal sbaccess_r    : std_logic_vector(2 downto 0)  := "010";
  signal sbreadonaddr_r : std_logic := '0';
  signal sbreadondata_r : std_logic := '0';
  signal sbautoincr_r   : std_logic := '0';
  signal sberror_r      : std_logic_vector(2 downto 0) := "000";
  signal sbbusyerror_r  : std_logic := '0';
  signal sbbusy_r       : std_logic := '0';
  signal sb_re_r        : std_logic := '0';
  signal sb_we_r        : std_logic := '0';
  signal sb_wdata_r     : std_logic_vector(63 downto 0) := (others => '0');

  signal rdata_r : std_logic_vector(31 downto 0) := (others => '0');
  signal ready_r : std_logic := '0';

begin

  process (clk, rst_n)
    variable dmstatus_v : std_logic_vector(31 downto 0);
    variable cmd_supported_v : boolean;
    variable is_gpr_v, is_dcsr_v, is_dpc_v, is_misa_v : boolean;
    variable is_mstatus_v, is_tselect_v, is_tdata1_v  : boolean;
    variable dcsr_v : std_logic_vector(31 downto 0);
    variable sbcs_v : std_logic_vector(31 downto 0);

    -- Launch an SBA bus access (read when wr=false, write when wr=true).
    -- No-op while a previous error is pending; flags sberror=4 on an
    -- unsupported sbaccess size. Caller must have checked sbbusy already.
    procedure sb_start(wr : boolean) is
    begin
      if sberror_r = "000" and sbbusyerror_r = '0' then
        if sbaccess_r /= "010" and sbaccess_r /= "011" then
          sberror_r <= "100";  -- 4 = unsupported size
        else
          sbbusy_r <= '1';
          if wr then
            sb_we_r <= '1';
          else
            sb_re_r <= '1';
          end if;
        end if;
      end if;
    end procedure sb_start;
  begin
    if rst_n = '0' then
      dmactive_r     <= '0';
      ndmreset_r     <= '0';
      haltreq_r      <= '0';
      havereset_r    <= '0';
      cmderr_r       <= "000";
      resume_pulse_r <= '0';
      data0_r        <= (others => '0');
      data1_r        <= (others => '0');
      abusy_r        <= '0';
      exec_write_r   <= '0';
      exec_size64_r  <= '0';
      gpr_re_r       <= '0';
      gpr_we_r       <= '0';
      gpr_regno_r    <= (others => '0');
      gpr_wdata_r    <= (others => '0');
      dpc_r          <= (others => '0');
      dcsr_ebreakm_r <= '0';
      dcsr_ebreaks_r <= '0';
      dcsr_ebreaku_r <= '0';
      dcsr_step_r    <= '0';
      dcsr_cause_r   <= "000";
      dcsr_prv_r     <= "11";
      step_pending_r <= '0';
      halted_q       <= '0';
      sbaddr_r       <= (others => '0');
      sbdata_r       <= (others => '0');
      sbaccess_r     <= "010";
      sbreadonaddr_r <= '0';
      sbreadondata_r <= '0';
      sbautoincr_r   <= '0';
      sberror_r      <= "000";
      sbbusyerror_r  <= '0';
      sbbusy_r       <= '0';
      sb_re_r        <= '0';
      sb_we_r        <= '0';
      sb_wdata_r     <= (others => '0');
      mstatus_r      <= (others => '0');
      rdata_r        <= (others => '0');
      ready_r        <= '0';
    elsif rising_edge(clk) then
      ready_r        <= '0';
      resume_pulse_r <= '0';

      -- Stage 4: capture dpc/dcsr.cause/dcsr.prv on the halted rising edge.
      halted_q <= halted_i;
      if halted_i = '1' and halted_q = '0' then
        dpc_r      <= pc_i;
        dcsr_prv_r <= prv_i;
        if ebreak_i = '1' then
          dcsr_cause_r <= "001";  -- 1 = ebreak
        elsif haltreq_r = '1' then
          dcsr_cause_r <= "011";  -- 3 = haltreq
        elsif step_pending_r = '1' then
          dcsr_cause_r <= "100";  -- 4 = step
        else
          dcsr_cause_r <= "011";
        end if;
        step_pending_r <= '0';
      end if;

      -- SBA completion: bus target acknowledged the access.
      if sbbusy_r = '1' and sb_ack_i = '1' then
        sb_re_r  <= '0';
        sb_we_r  <= '0';
        sbbusy_r <= '0';
        if sb_err_i = '1' then
          sberror_r <= "010";  -- 2 = bad address
        else
          if sb_re_r = '1' then
            if sbaccess_r = "011" then
              sbdata_r <= sb_rdata_i;
            else
              sbdata_r(31 downto 0) <= sb_rdata_i(31 downto 0);
            end if;
          end if;
          if sbautoincr_r = '1' then
            if sbaccess_r = "011" then
              sbaddr_r <= std_logic_vector(unsigned(sbaddr_r) + 8);
            else
              sbaddr_r <= std_logic_vector(unsigned(sbaddr_r) + 4);
            end if;
          end if;
        end if;
      end if;

      -- Abstract command completion: hart acknowledged the GPR access.
      if abusy_r = '1' and gpr_ack_i = '1' then
        gpr_re_r <= '0';
        gpr_we_r <= '0';
        abusy_r  <= '0';
        if exec_write_r = '0' then
          data0_r <= gpr_rdata_i(31 downto 0);
          if exec_size64_r = '1' then
            data1_r <= gpr_rdata_i(63 downto 32);
          end if;
        end if;
      end if;

      if dmi_valid = '1' then
        ready_r <= '1';

        if dmi_op = "10" then  -- write
          if dmi_addr = A_DMCONTROL then
            if dmi_wdata(0) = '0' then
              -- dmactive=0: full DM reset; every other bit ignored.
              dmactive_r  <= '0';
              ndmreset_r  <= '0';
              haltreq_r   <= '0';
              havereset_r <= '0';
              cmderr_r    <= "000";
              data0_r     <= (others => '0');
              data1_r     <= (others => '0');
              abusy_r     <= '0';
              gpr_re_r    <= '0';
              gpr_we_r    <= '0';
              dpc_r          <= (others => '0');
              dcsr_ebreakm_r <= '0';
              dcsr_ebreaks_r <= '0';
              dcsr_ebreaku_r <= '0';
              dcsr_step_r    <= '0';
              dcsr_cause_r   <= "000";
              dcsr_prv_r     <= "11";
              step_pending_r <= '0';
              sbaddr_r       <= (others => '0');
              sbdata_r       <= (others => '0');
              sbaccess_r     <= "010";
              sbreadonaddr_r <= '0';
              sbreadondata_r <= '0';
              sbautoincr_r   <= '0';
              sberror_r      <= "000";
              sbbusyerror_r  <= '0';
              sbbusy_r       <= '0';
              sb_re_r        <= '0';
              sb_we_r        <= '0';
              mstatus_r      <= (others => '0');
            else
              dmactive_r <= '1';
              if dmactive_r = '1' then
                -- Other fields honored only once DM already active.
                haltreq_r  <= dmi_wdata(31);
                if dmi_wdata(30) = '1' then
                  resume_pulse_r <= '1';
                  if dcsr_step_r = '1' then
                    step_pending_r <= '1';  -- arm single-step re-halt cause
                  end if;
                end if;
                if dmi_wdata(1) = '1' and ndmreset_r = '0' then
                  havereset_r <= '1';  -- ndmreset 0->1: hart has been reset
                end if;
                ndmreset_r <= dmi_wdata(1);
                if dmi_wdata(28) = '1' then
                  havereset_r <= '0';  -- ackhavereset
                end if;
              end if;
            end if;
          elsif dmi_addr = A_DATA0 then
            if dmactive_r = '1' then
              if abusy_r = '1' then
                if cmderr_r = "000" then
                  cmderr_r <= "001";  -- busy violation; write dropped
                end if;
              else
                data0_r <= dmi_wdata;
              end if;
            end if;
          elsif dmi_addr = A_DATA1 then
            if dmactive_r = '1' then
              if abusy_r = '1' then
                if cmderr_r = "000" then
                  cmderr_r <= "001";  -- busy violation; write dropped
                end if;
              else
                data1_r <= dmi_wdata;
              end if;
            end if;
          elsif dmi_addr = A_ABSTRACTCS then
            if dmactive_r = '1' then
              cmderr_r <= cmderr_r and not dmi_wdata(10 downto 8);  -- W1C
            end if;
          elsif dmi_addr = A_COMMAND then
            if dmactive_r = '1' then
              if abusy_r = '1' then
                if cmderr_r = "000" then
                  cmderr_r <= "001";  -- busy violation
                end if;
              elsif cmderr_r /= "000" then
                null;  -- sticky: command ignored until cmderr cleared (W1C)
              else
                -- Decode access-register command.
                is_gpr_v  := dmi_wdata(15 downto 5) = "00010000000"; -- 0x1000..0x101F
                is_dcsr_v := dmi_wdata(15 downto 0) = x"07B0";       -- dcsr
                is_dpc_v  := dmi_wdata(15 downto 0) = x"07B1";       -- dpc
                is_misa_v := dmi_wdata(15 downto 0) = x"0301";       -- misa
                is_mstatus_v := dmi_wdata(15 downto 0) = x"0300";    -- mstatus
                is_tselect_v := dmi_wdata(15 downto 0) = x"07A0";    -- tselect
                is_tdata1_v  := dmi_wdata(15 downto 0) = x"07A1";    -- tdata1
                cmd_supported_v :=
                  dmi_wdata(31 downto 24) = x"00"                -- cmdtype 0
                  and (dmi_wdata(22 downto 20) = "010"           -- aarsize 2
                       or dmi_wdata(22 downto 20) = "011")       -- aarsize 3
                  and (dmi_wdata(17) = '0'                       -- no transfer
                       or is_gpr_v
                       or is_dcsr_v
                       or is_dpc_v
                       or is_mstatus_v
                       or is_tselect_v
                       or ((is_misa_v or is_tdata1_v)
                           and dmi_wdata(16) = '0'));            -- RO stubs
                if not cmd_supported_v then
                  cmderr_r <= "010";  -- 2 = not supported
                elsif halted_i = '0' then
                  cmderr_r <= "100";  -- 4 = hart not halted
                elsif dmi_wdata(17) = '1' then
                  if is_gpr_v then
                    -- Launch GPR access (transfer=0 is a successful no-op).
                    abusy_r       <= '1';
                    exec_size64_r <= dmi_wdata(20);  -- '0'=32-bit, '1'=64-bit
                    gpr_regno_r   <= dmi_wdata(4 downto 0);
                    if dmi_wdata(16) = '1' then
                      exec_write_r <= '1';
                      gpr_we_r     <= '1';
                      if dmi_wdata(20) = '1' then
                        gpr_wdata_r <= data1_r & data0_r;
                      else
                        gpr_wdata_r <= x"00000000" & data0_r;  -- zero-extend
                      end if;
                    else
                      exec_write_r <= '0';
                      gpr_re_r     <= '1';
                    end if;
                  elsif is_dcsr_v then
                    -- DM-resident CSR: completes immediately, no busy.
                    if dmi_wdata(16) = '1' then
                      dcsr_ebreakm_r <= data0_r(15);
                      dcsr_ebreaks_r <= data0_r(13);
                      dcsr_ebreaku_r <= data0_r(12);
                      dcsr_step_r    <= data0_r(2);
                      if data0_r(1 downto 0) /= "10" then
                        dcsr_prv_r <= data0_r(1 downto 0);  -- WARL 0/1/3
                      end if;
                    else
                      dcsr_v := (others => '0');
                      dcsr_v(31 downto 28) := "0100";  -- xdebugver = 4
                      dcsr_v(15)           := dcsr_ebreakm_r;
                      dcsr_v(13)           := dcsr_ebreaks_r;
                      dcsr_v(12)           := dcsr_ebreaku_r;
                      dcsr_v(8 downto 6)   := dcsr_cause_r;
                      dcsr_v(2)            := dcsr_step_r;
                      dcsr_v(1 downto 0)   := dcsr_prv_r;
                      data0_r <= dcsr_v;
                      if dmi_wdata(20) = '1' then
                        data1_r <= (others => '0');  -- aarsize=3: zero-extend
                      end if;
                    end if;
                  elsif is_misa_v then
                    -- Read-only stub CSR (writes rejected in the decode).
                    data0_r <= MISA_VALUE(31 downto 0);
                    if dmi_wdata(20) = '1' then
                      data1_r <= MISA_VALUE(63 downto 32);
                    end if;
                  elsif is_mstatus_v then
                    if dmi_wdata(16) = '1' then
                      if dmi_wdata(20) = '1' then
                        mstatus_r <= data1_r & data0_r;
                      else
                        mstatus_r <= x"00000000" & data0_r;  -- zero-extend
                      end if;
                    else
                      data0_r <= mstatus_r(31 downto 0);
                      if dmi_wdata(20) = '1' then
                        data1_r <= mstatus_r(63 downto 32);
                      end if;
                    end if;
                  elsif is_tselect_v or is_tdata1_v then
                    -- tselect: WARL write accepted + ignored, reads 0.
                    -- tdata1: reads 0 (type=0 -> no trigger implemented).
                    if dmi_wdata(16) = '0' then
                      data0_r <= (others => '0');
                      if dmi_wdata(20) = '1' then
                        data1_r <= (others => '0');
                      end if;
                    end if;
                  else  -- is_dpc_v
                    if dmi_wdata(16) = '1' then
                      if dmi_wdata(20) = '1' then
                        dpc_r <= data1_r & data0_r;
                      else
                        dpc_r <= x"00000000" & data0_r;  -- zero-extend
                      end if;
                    else
                      data0_r <= dpc_r(31 downto 0);
                      if dmi_wdata(20) = '1' then
                        data1_r <= dpc_r(63 downto 32);
                      end if;
                    end if;
                  end if;
                end if;
              end if;
            end if;
          elsif dmi_addr = A_SBCS then
            if dmactive_r = '1' then
              sbbusyerror_r <= sbbusyerror_r and not dmi_wdata(22);  -- W1C
              sberror_r <= sberror_r and not dmi_wdata(14 downto 12);  -- W1C
              if sbbusy_r = '0' then
                sbreadonaddr_r <= dmi_wdata(20);
                sbaccess_r     <= dmi_wdata(19 downto 17);
                sbautoincr_r   <= dmi_wdata(16);
                sbreadondata_r <= dmi_wdata(15);
              end if;
            end if;
          elsif dmi_addr = A_SBADDRESS0 then
            if dmactive_r = '1' then
              if sbbusy_r = '1' then
                sbbusyerror_r <= '1';
              else
                sbaddr_r(31 downto 0) <= dmi_wdata;
                if sbreadonaddr_r = '1' then
                  sb_start(wr => false);
                end if;
              end if;
            end if;
          elsif dmi_addr = A_SBADDRESS1 then
            if dmactive_r = '1' then
              if sbbusy_r = '1' then
                sbbusyerror_r <= '1';
              else
                sbaddr_r(63 downto 32) <= dmi_wdata;
              end if;
            end if;
          elsif dmi_addr = A_SBDATA0 then
            if dmactive_r = '1' then
              if sbbusy_r = '1' then
                sbbusyerror_r <= '1';
              elsif sberror_r = "000" and sbbusyerror_r = '0' then
                sbdata_r(31 downto 0) <= dmi_wdata;
                if sbaccess_r = "011" then
                  sb_wdata_r <= sbdata_r(63 downto 32) & dmi_wdata;
                else
                  sb_wdata_r <= x"00000000" & dmi_wdata;
                end if;
                sb_start(wr => true);
              end if;
            end if;
          elsif dmi_addr = A_SBDATA1 then
            if dmactive_r = '1' then
              if sbbusy_r = '1' then
                sbbusyerror_r <= '1';
              else
                sbdata_r(63 downto 32) <= dmi_wdata;
              end if;
            end if;
          end if;
          -- other addresses: write ignored

        elsif dmi_op = "01" then  -- read
          rdata_r <= (others => '0');
          if dmi_addr = A_DMCONTROL then
            if dmactive_r = '1' then
              rdata_r(0) <= '1';
              rdata_r(1) <= ndmreset_r;
            end if;
          elsif dmi_addr = A_DMSTATUS then
            dmstatus_v := (others => '0');
            dmstatus_v(3 downto 0) := "0010";  -- version 2 = spec 0.13
            dmstatus_v(7) := '1';              -- authenticated (no auth unit)
            if dmactive_r = '1' then
              dmstatus_v(8)  := halted_i;      -- anyhalted
              dmstatus_v(9)  := halted_i;      -- allhalted
              dmstatus_v(10) := running_i;     -- anyrunning
              dmstatus_v(11) := running_i;     -- allrunning
              dmstatus_v(16) := resumeack_i;   -- anyresumeack
              dmstatus_v(17) := resumeack_i;   -- allresumeack
              dmstatus_v(18) := havereset_r;   -- anyhavereset
              dmstatus_v(19) := havereset_r;   -- allhavereset
            end if;
            rdata_r <= dmstatus_v;
          elsif dmi_addr = A_DATA0 then
            rdata_r <= data0_r;
          elsif dmi_addr = A_DATA1 then
            rdata_r <= data1_r;
          elsif dmi_addr = A_ABSTRACTCS then
            rdata_r(3 downto 0)   <= "0010";  -- datacount = 2
            rdata_r(12)           <= abusy_r;
            rdata_r(10 downto 8)  <= cmderr_r;
          elsif dmi_addr = A_SBCS then
            sbcs_v := (others => '0');
            sbcs_v(31 downto 29) := "001";           -- sbversion = 1
            sbcs_v(22)           := sbbusyerror_r;
            sbcs_v(21)           := sbbusy_r;
            sbcs_v(20)           := sbreadonaddr_r;
            sbcs_v(19 downto 17) := sbaccess_r;
            sbcs_v(16)           := sbautoincr_r;
            sbcs_v(15)           := sbreadondata_r;
            sbcs_v(14 downto 12) := sberror_r;
            sbcs_v(11 downto 5)  := "1000000";       -- sbasize = 64
            sbcs_v(3)            := '1';             -- sbaccess64
            sbcs_v(2)            := '1';             -- sbaccess32
            rdata_r <= sbcs_v;
          elsif dmi_addr = A_SBADDRESS0 then
            rdata_r <= sbaddr_r(31 downto 0);
          elsif dmi_addr = A_SBADDRESS1 then
            rdata_r <= sbaddr_r(63 downto 32);
          elsif dmi_addr = A_SBDATA0 then
            rdata_r <= sbdata_r(31 downto 0);
            if dmactive_r = '1' then
              if sbbusy_r = '1' then
                sbbusyerror_r <= '1';
              elsif sbreadondata_r = '1' then
                sb_start(wr => false);
              end if;
            end if;
          elsif dmi_addr = A_SBDATA1 then
            rdata_r <= sbdata_r(63 downto 32);
          end if;
          -- HARTINFO and all other 0x1x registers read as 0
        end if;
      end if;
    end if;
  end process;

  dmi_rdata <= rdata_r;
  dmi_resp  <= "00";  -- all DM-range accesses succeed
  dmi_ready <= ready_r;

  dmactive_o        <= dmactive_r;
  ndmreset_o        <= ndmreset_r;
  haltreq_o         <= haltreq_r;
  resumereq_pulse_o <= resume_pulse_r;

  gpr_re_o    <= gpr_re_r;
  gpr_we_o    <= gpr_we_r;
  gpr_regno_o <= gpr_regno_r;
  gpr_wdata_o <= gpr_wdata_r;

  dpc_o  <= dpc_r;
  step_o <= dcsr_step_r;

  sb_re_o    <= sb_re_r;
  sb_we_o    <= sb_we_r;
  sb_addr_o  <= sbaddr_r;
  sb_wdata_o <= sb_wdata_r;
  sb_size_o  <= sbaccess_r(1 downto 0);

end architecture rtl;
