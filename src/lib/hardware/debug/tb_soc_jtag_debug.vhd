-- tb_soc_jtag_debug.vhd — Lane B: end-to-end SoC JTAG debug through the RAW TAP.
--
-- Drives the FULL board transport chain the way OpenOCD will on hardware:
--
--   raw JTAG (TCK) -> jtag_tap -> riscv_dtm ==CDC(tck→clk)==> dmi_bus -> DM -> rv32 hart
--
-- i.e. the jtag_debug_chain bundle, exercised over serial TMS/TDI/TDO scans
-- (NOT direct DMI writes) with **TCK 8x slower than the core clk** so the
-- tck→clk clock-domain-crossing in jtag_debug_chain is genuinely stressed —
-- this is the case a real debug probe creates and the single-clock Stage tbs
-- never covered.
--
-- Program staged by the harness in rv32_payload.mem (see run_hart_e2e / the
-- validate script):
--   0x00: addi x10,x0,42 (0x02A00513)   0x04: addi x1,x0,7 (0x00700093)   NOP sled
--
-- OpenOCD-equivalent operations proven, each backed by assert...failure:
--   EXAMINE  IDCODE scan = 0x15350067; DTMCS version=1, abits=7
--   HALT     hart halted out of reset (dmstatus allhalted)
--   READPC   dpc abstract read returns the real full-width reset pc (bit31=1)
--   READGPR  x10 and x1 abstract-read as 0 at reset
--   STEP1    dcsr.step=1 + resume -> re-halt: pc+4, x10 (a0) 0 -> 42
--   STEP2    second step -> pc+8, x1 (ra) 0 -> 7  (GPR readback after execution)
--   RESUME   clear step, resume (free-run), haltreq -> re-halt, read pc
--
-- Prints per-op PASS notes and "SOC JTAG DEBUG: ALL PASS" only if every assert
-- held (evidence rule: the ALL-PASS marker is unreachable on any failure because
-- asserts are severity failure and stop the run).

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use std.textio.all;
use std.env.all;

entity tb_soc_jtag_debug is
end entity tb_soc_jtag_debug;

architecture sim of tb_soc_jtag_debug is
  constant CLK_PERIOD    : time := 10 ns;   -- 100 MHz-ish core clk
  constant EXPECTED_IDCODE : std_logic_vector(31 downto 0) := x"15350067";

  signal clk    : std_logic := '0';
  signal rst_n  : std_logic := '0';

  signal tck    : std_logic := '0';
  signal tms    : std_logic := '0';
  signal tdi    : std_logic := '0';
  signal trst_n : std_logic := '0';
  signal tdo    : std_logic;

  signal uart_tx        : std_logic;
  signal o_halted       : std_logic;
  signal o_running      : std_logic;
  signal o_step         : std_logic;
  signal o_dbg_pc_full  : std_logic_vector(31 downto 0);
  signal o_dbg_reg_data : std_logic_vector(31 downto 0);

  -- JTAG instructions (5-bit IR) — must match riscv_dtm / jtag_tap decode.
  constant IR_IDCODE : std_logic_vector(4 downto 0) := "00001";
  constant IR_DTMCS  : std_logic_vector(4 downto 0) := "10000";
  constant IR_DMI    : std_logic_vector(4 downto 0) := "10001";

  -- DMI register addresses (RISC-V debug v0.13) — same as tb_hart_integration.
  constant A_DATA0      : std_logic_vector(6 downto 0) := "0000100";  -- 0x04
  constant A_DATA1      : std_logic_vector(6 downto 0) := "0000101";  -- 0x05
  constant A_DMCONTROL  : std_logic_vector(6 downto 0) := "0010000";  -- 0x10
  constant A_DMSTATUS   : std_logic_vector(6 downto 0) := "0010001";  -- 0x11
  constant A_ABSTRACTCS : std_logic_vector(6 downto 0) := "0010110";  -- 0x16
  constant A_COMMAND    : std_logic_vector(6 downto 0) := "0010111";  -- 0x17
begin
  clk <= not clk after CLK_PERIOD / 2;

  dut : entity work.jtag_debug_chain
    generic map (IDCODE_VALUE => EXPECTED_IDCODE)
    port map (
      clk => clk, rst_n => rst_n,
      tck => tck, tms => tms, tdi => tdi, trst_n => trst_n, tdo => tdo,
      uart_tx => uart_tx,
      o_halted => o_halted, o_running => o_running, o_step => o_step,
      o_dbg_pc_full => o_dbg_pc_full, o_dbg_reg_data => o_dbg_reg_data);

  stim : process
    variable l : line;

    -- One TCK cycle. TCK LOW = 25 ns, HIGH = 30 ns => 80 ns period = 8x the
    -- 10 ns core clk, so the CDC synchronizers cross a genuinely slower TCK.
    procedure jtag_cycle(tms_v : std_logic; tdi_v : std_logic) is
    begin
      tms <= tms_v; tdi <= tdi_v;
      wait for 25 ns;   -- setup during TCK low
      tck <= '1';
      wait for 30 ns;   -- TCK high
      tck <= '0';
      wait for 25 ns;   -- TCK low tail (TDO settles by falling edge)
    end procedure;

    procedure idle_cycles(n : natural) is
    begin
      for k in 1 to n loop jtag_cycle('0', '0'); end loop;
    end procedure;

    -- DR scan RTI->RTI, LSB-first; din/dout indexed (N-1 downto 0), bit0 first.
    procedure scan_dr(din : in std_logic_vector; dout : out std_logic_vector) is
    begin
      jtag_cycle('1', '0');   -- RTI -> Select-DR
      jtag_cycle('0', '0');   -- -> Capture-DR
      jtag_cycle('0', '0');   -- -> Shift-DR (capture here)
      for i in 0 to din'length - 1 loop
        dout(i) := tdo;
        if i = din'length - 1 then
          jtag_cycle('1', din(i));   -- last shift, exit
        else
          jtag_cycle('0', din(i));
        end if;
      end loop;
      jtag_cycle('1', '0');   -- Exit1-DR -> Update-DR
      jtag_cycle('0', '0');   -- Update-DR -> RTI (update here)
    end procedure;

    procedure scan_ir(insn : in std_logic_vector(4 downto 0)) is
    begin
      jtag_cycle('1', '0');   -- RTI -> Select-DR
      jtag_cycle('1', '0');   -- -> Select-IR
      jtag_cycle('0', '0');   -- -> Capture-IR
      jtag_cycle('0', '0');   -- -> Shift-IR
      for i in 0 to 4 loop
        if i = 4 then jtag_cycle('1', insn(i)); else jtag_cycle('0', insn(i)); end if;
      end loop;
      jtag_cycle('1', '0');   -- Exit1-IR -> Update-IR
      jtag_cycle('0', '0');   -- Update-IR -> RTI
    end procedure;

    variable din32  : std_logic_vector(31 downto 0);
    variable dout32 : std_logic_vector(31 downto 0);
    variable din41  : std_logic_vector(40 downto 0);
    variable dout41 : std_logic_vector(40 downto 0);

    -- DMI write: issue op=10 then settle. Assumes DMI IR already selected.
    procedure dmi_write(a : std_logic_vector(6 downto 0);
                        d : std_logic_vector(31 downto 0)) is
      variable q : std_logic_vector(40 downto 0);
    begin
      din41 := a & d & "10";
      scan_dr(din41, q);
      idle_cycles(20);        -- CDC + DM complete before next scan
    end procedure;

    -- DMI read: issue op=01, settle, then nop-scan to capture data+status.
    -- Retries once on a busy(op=11) capture (should not occur with the idle
    -- window, but keeps the read robust exactly like a real driver).
    procedure dmi_read(a : std_logic_vector(6 downto 0);
                       d : out std_logic_vector(31 downto 0)) is
      variable q : std_logic_vector(40 downto 0);
      variable tries : natural := 0;
    begin
      din41 := a & x"00000000" & "01";
      scan_dr(din41, q);           -- issue read
      idle_cycles(20);
      loop
        din41 := (others => '0');  -- nop: collect result
        scan_dr(din41, q);
        exit when q(1 downto 0) = "00";
        assert q(1 downto 0) = "11"
          report "DMI read status /= success/busy, op=" & to_string(q(1 downto 0))
          severity failure;
        tries := tries + 1;
        assert tries < 8 report "DMI read stuck busy" severity failure;
        idle_cycles(20);
      end loop;
      d := q(33 downto 2);
    end procedure;

    procedure wait_cmd_done is
      variable r : std_logic_vector(31 downto 0);
    begin
      for i in 0 to 64 loop
        dmi_read(A_ABSTRACTCS, r);
        exit when r(12) = '0';   -- busy
        assert i < 64 report "abstract command stuck busy" severity failure;
      end loop;
      assert r(10 downto 8) = "000"
        report "abstract cmderr /= 0, ABSTRACTCS=0x" & to_hstring(r) severity failure;
    end procedure;

    procedure read_gpr(regno : natural; data : out std_logic_vector(31 downto 0)) is
    begin
      dmi_write(A_COMMAND, x"00221000" or std_logic_vector(to_unsigned(regno, 32)));
      wait_cmd_done;
      dmi_read(A_DATA0, data);
    end procedure;

    procedure read_dpc(lo : out std_logic_vector(31 downto 0);
                       hi : out std_logic_vector(31 downto 0)) is
    begin
      dmi_write(A_COMMAND, x"003207B1");   -- read dpc, aarsize=3
      wait_cmd_done;
      dmi_read(A_DATA0, lo);
      dmi_read(A_DATA1, hi);
    end procedure;

    variable rd       : std_logic_vector(31 downto 0);
    variable dpc_lo   : std_logic_vector(31 downto 0);
    variable dpc_hi   : std_logic_vector(31 downto 0);
    variable pc0, pc1, pc2 : unsigned(31 downto 0);
  begin
    -- Reset both domains.
    trst_n <= '0'; rst_n <= '0';
    wait for 200 ns;
    trst_n <= '1'; rst_n <= '1';
    for i in 0 to 8 loop wait until rising_edge(clk); end loop;

    -- The TAP powers up in Test-Logic-Reset. Force TLR (5x TMS=1) then drop to
    -- Run-Test/Idle, which is where scan_ir/scan_dr assume the FSM starts.
    for k in 1 to 5 loop jtag_cycle('1', '0'); end loop;   -- -> TLR
    jtag_cycle('0', '0');                                   -- TLR -> RTI

    ------------------------------------------------------------------ EXAMINE
    din32 := (others => '0');
    scan_ir(IR_IDCODE);
    scan_dr(din32, dout32);
    assert dout32 = EXPECTED_IDCODE
      report "EXAMINE FAIL: IDCODE=0x" & to_hstring(dout32) severity failure;
    scan_ir(IR_DTMCS);
    scan_dr(din32, dout32);
    assert dout32(3 downto 0) = "0001" and dout32(9 downto 4) = "000111"
      report "EXAMINE FAIL: DTMCS=0x" & to_hstring(dout32) severity failure;
    report "EXAMINE PASS: IDCODE=0x" & to_hstring(EXPECTED_IDCODE)
      & " DTMCS version=1 abits=7 (through raw TAP)" severity note;

    scan_ir(IR_DMI);                       -- DMI selected for the rest
    dmi_write(A_DMCONTROL, x"00000001");   -- dmactive=1

    ------------------------------------------------------------------ HALT
    assert o_halted = '1'
      report "HALT FAIL: hart not halted out of reset" severity failure;
    dmi_read(A_DMSTATUS, rd);
    assert rd(9) = '1'                     -- allhalted
      report "HALT FAIL: dmstatus.allhalted clear, =0x" & to_hstring(rd) severity failure;
    report "HALT PASS: hart halted (dmstatus.allhalted, via JTAG)" severity note;

    ------------------------------------------------------------------ READPC / READGPR
    read_dpc(dpc_lo, dpc_hi);
    pc0 := unsigned(dpc_lo);
    assert pc0(31) = '1' and dpc_hi = x"00000000"
      report "READPC FAIL: dpc not full reset pc, hi=0x" & to_hstring(dpc_hi)
             & " lo=0x" & to_hstring(dpc_lo) severity failure;
    report "READPC PASS: dpc=0x" & to_hstring(dpc_lo) & " (full-width, via JTAG)"
      severity note;
    read_gpr(10, rd);
    assert rd = x"00000000" report "READGPR FAIL: x10 /= 0 at reset" severity failure;
    read_gpr(1, rd);
    assert rd = x"00000000" report "READGPR FAIL: x1 /= 0 at reset" severity failure;
    report "READGPR PASS: x10=0 x1=0 at reset (abstract cmd via JTAG)" severity note;

    ------------------------------------------------------------------ STEP1
    dmi_write(A_DATA0, x"00000007");       -- dcsr.step=1, prv=3
    dmi_write(A_COMMAND, x"002307B0");
    wait_cmd_done;
    dmi_write(A_DMCONTROL, x"40000001");   -- resumereq=1 (single step)
    for i in 0 to 40 loop
      dmi_read(A_DMSTATUS, rd);
      exit when rd(9) = '1';
      assert i < 40 report "STEP1 FAIL: no re-halt after step 1" severity failure;
    end loop;
    read_dpc(dpc_lo, dpc_hi); pc1 := unsigned(dpc_lo);
    read_gpr(10, rd);
    assert (pc1 - pc0) = 4
      report "STEP1 FAIL: pc advanced by " & integer'image(to_integer(pc1 - pc0))
      severity failure;
    assert rd = x"0000002A"
      report "STEP1 FAIL: x10 (a0) /= 42, got 0x" & to_hstring(rd) severity failure;
    write(l, string'("  STEP1: pc 0x")); hwrite(l, dpc_lo);
    write(l, string'("  a0 0 -> ")); write(l, to_integer(unsigned(rd)));
    writeline(output, l);
    report "STEP1 PASS: one insn retired (pc+4), x10 (a0)=42" severity note;

    ------------------------------------------------------------------ STEP2
    dmi_write(A_DMCONTROL, x"40000001");   -- step again (dcsr.step still 1)
    for i in 0 to 40 loop
      dmi_read(A_DMSTATUS, rd);
      exit when rd(9) = '1';
      assert i < 40 report "STEP2 FAIL: no re-halt after step 2" severity failure;
    end loop;
    read_dpc(dpc_lo, dpc_hi); pc2 := unsigned(dpc_lo);
    read_gpr(1, rd);
    assert (pc2 - pc1) = 4
      report "STEP2 FAIL: pc advanced by " & integer'image(to_integer(pc2 - pc1))
      severity failure;
    assert rd = x"00000007"
      report "STEP2 FAIL: x1 (ra) /= 7, got 0x" & to_hstring(rd) severity failure;
    report "STEP2 PASS: second insn retired (pc+8 total), x1 (ra)=7" severity note;

    ------------------------------------------------------------------ RESUME
    dmi_write(A_DATA0, x"00000003");       -- dcsr.step=0
    dmi_write(A_COMMAND, x"002307B0");
    wait_cmd_done;
    dmi_write(A_DMCONTROL, x"40000001");   -- resumereq -> free run
    for i in 0 to 40 loop wait until rising_edge(clk); end loop;
    assert o_running = '1'
      report "RESUME FAIL: hart not running after resume" severity failure;
    dmi_write(A_DMCONTROL, x"80000001");   -- haltreq=1
    for i in 0 to 40 loop
      dmi_read(A_DMSTATUS, rd);
      exit when rd(9) = '1';
      assert i < 40 report "RESUME FAIL: haltreq did not re-halt" severity failure;
    end loop;
    read_dpc(dpc_lo, dpc_hi);
    assert dpc_lo(31) = '1'
      report "RESUME FAIL: post-halt pc not in ROM, =0x" & to_hstring(dpc_lo)
      severity failure;
    report "RESUME PASS: free-run then haltreq re-halted, pc=0x" & to_hstring(dpc_lo)
      severity note;

    report "SOC JTAG DEBUG: ALL PASS" severity note;
    finish;
  end process;

end architecture sim;
