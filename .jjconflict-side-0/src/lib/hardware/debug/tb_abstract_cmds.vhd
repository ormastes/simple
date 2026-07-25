-- tb_abstract_cmds.vhd — Stage-3 testbench: abstract commands + GPR access.
--
-- Stage 4 re-point: drives the DM THROUGH the real dmi_bus. dmi_bus now
-- forwards the abstract-data window 0x04..0x0B and 0x10..0x1F to the DM
-- (its Stage-1 scratch shrank to 0x00..0x03), so DATA0/DATA1 (0x04/0x05)
-- are reachable through the bus — CHECK1..CHECK5 exercise that routing.
-- A fake hart answers haltreq/resumereq with a few cycles of latency and
-- models a 32 x 64-bit GPR regfile on the Stage-3 GPR port (2-cycle ack
-- latency; x0 writes accepted but dropped so x0 stays 0).
--
-- Checks:
--   CHECK1: halted hart: DATA0=0xCAFEBABE, COMMAND write x5 (aarsize=2)
--           -> fake regfile x5 == 0x00000000CAFEBABE (zero-extended)
--   CHECK2: COMMAND read x5 (aarsize=2) -> DATA0 == 0xCAFEBABE
--   CHECK3: 64-bit: DATA0+DATA1 -> COMMAND write x6 (aarsize=3), read back
--           both halves via COMMAND read x6
--   CHECK4: running hart: COMMAND -> cmderr=4 (haltresume); W1C clears
--   CHECK5: bad regno 0x2000 -> cmderr=2 (not supported); W1C clears
--   CHECK6: Stage-2 regression (in-bench): halt/resume handshake exercised
--           by CHECK1/4 preambles + ndmreset -> havereset -> ackhavereset;
--           full tb_debug_module run is the external regression gate
--   CHECK7: Stage-1 regression (in-bench): dmi_bus scratch round-trips at
--           0x00 and 0x03 (Stage-4 scratch range; 0x04 now routes to the
--           DM as DATA0 — the old collision is gone); full tb_jtag_dtm_dmi
--           run is the external gate
-- Ends with: report "JTAG STAGE3 PASS"

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use std.env.all;

entity tb_abstract_cmds is
end entity tb_abstract_cmds;

architecture sim of tb_abstract_cmds is

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

  -- dmi_bus <-> debug module
  signal dm_valid : std_logic;
  signal dm_addr  : std_logic_vector(6 downto 0);
  signal dm_wdata : std_logic_vector(31 downto 0);
  signal dm_op    : std_logic_vector(1 downto 0);
  signal dm_rdata : std_logic_vector(31 downto 0);
  signal dm_resp  : std_logic_vector(1 downto 0);
  signal dm_ready : std_logic;

  -- DM <-> fake hart (halt/resume)
  signal haltreq_s   : std_logic;
  signal resumereq_s : std_logic;
  signal ndmreset_s  : std_logic;
  signal halted_s    : std_logic;
  signal running_s   : std_logic;

  signal hart_halted : std_logic := '0';

  -- DM <-> fake hart (Stage-3 GPR port)
  signal gpr_re_s    : std_logic;
  signal gpr_we_s    : std_logic;
  signal gpr_regno_s : std_logic_vector(4 downto 0);
  signal gpr_wdata_s : std_logic_vector(63 downto 0);
  signal gpr_rdata_s : std_logic_vector(63 downto 0) := (others => '0');
  signal gpr_ack_s   : std_logic := '0';

  type regfile_t is array (0 to 31) of std_logic_vector(63 downto 0);
  signal regs : regfile_t := (others => (others => '0'));

  constant A_DATA0      : std_logic_vector(6 downto 0) := "0000100";  -- 0x04
  constant A_DATA1      : std_logic_vector(6 downto 0) := "0000101";  -- 0x05
  constant A_DMCONTROL  : std_logic_vector(6 downto 0) := "0010000";  -- 0x10
  constant A_DMSTATUS   : std_logic_vector(6 downto 0) := "0010001";  -- 0x11
  constant A_ABSTRACTCS : std_logic_vector(6 downto 0) := "0010110";  -- 0x16
  constant A_COMMAND    : std_logic_vector(6 downto 0) := "0010111";  -- 0x17
  constant A_SCRATCH0   : std_logic_vector(6 downto 0) := "0000000";  -- 0x00
  constant A_SCRATCH3   : std_logic_vector(6 downto 0) := "0000011";  -- 0x03

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
      haltreq_o => haltreq_s, resumereq_o => resumereq_s,
      ndmreset_o => ndmreset_s,
      halted_i => halted_s, running_i => running_s,
      gpr_re_o => gpr_re_s, gpr_we_o => gpr_we_s,
      gpr_regno_o => gpr_regno_s, gpr_wdata_o => gpr_wdata_s,
      gpr_rdata_i => gpr_rdata_s, gpr_ack_i => gpr_ack_s);

  -- Fake hart: haltreq -> halted after 3 cycles; resumereq -> running after 3.
  fake_hart : process (clk, rst_n)
    variable cnt : natural := 0;
  begin
    if rst_n = '0' then
      hart_halted <= '0';
      cnt := 0;
    elsif rising_edge(clk) then
      if hart_halted = '0' and haltreq_s = '1' then
        if cnt = 3 then
          hart_halted <= '1';
          cnt := 0;
        else
          cnt := cnt + 1;
        end if;
      elsif hart_halted = '1' and resumereq_s = '1' then
        if cnt = 3 then
          hart_halted <= '0';
          cnt := 0;
        else
          cnt := cnt + 1;
        end if;
      else
        cnt := 0;
      end if;
    end if;
  end process fake_hart;

  halted_s  <= hart_halted;
  running_s <= not hart_halted;

  -- Fake 32 x 64-bit GPR regfile: ack after 2 cycles of re/we held high.
  -- Writes to x0 are accepted (acked) but dropped so x0 stays 0.
  gpr_model : process (clk, rst_n)
    variable cnt : natural := 0;
  begin
    if rst_n = '0' then
      gpr_ack_s   <= '0';
      gpr_rdata_s <= (others => '0');
      cnt := 0;
    elsif rising_edge(clk) then
      gpr_ack_s <= '0';
      if (gpr_re_s = '1' or gpr_we_s = '1') and gpr_ack_s = '0' then
        if cnt = 2 then
          cnt := 0;
          gpr_ack_s <= '1';
          if gpr_we_s = '1' then
            if to_integer(unsigned(gpr_regno_s)) /= 0 then
              regs(to_integer(unsigned(gpr_regno_s))) <= gpr_wdata_s;
            end if;
          else
            gpr_rdata_s <= regs(to_integer(unsigned(gpr_regno_s)));
          end if;
        else
          cnt := cnt + 1;
        end if;
      else
        cnt := 0;
      end if;
    end if;
  end process gpr_model;

  stim : process
    variable rd : std_logic_vector(31 downto 0);

    -- One DMI transaction through dmi_bus (Stage 4: scratch, data window
    -- and DM regs all share this path): valid for 1 clock, response
    -- registered 1 clock later; sample mid response cycle.
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

    -- Poll ABSTRACTCS until busy=0; also require cmderr=0.
    procedure wait_cmd_done is
      variable r     : std_logic_vector(31 downto 0);
      variable polls : natural := 0;
    begin
      loop
        dmi_read(A_ABSTRACTCS, r);
        exit when r(12) = '0';
        polls := polls + 1;
        assert polls < 25
          report "abstract command stuck busy, ABSTRACTCS=0x" & to_hstring(r)
          severity failure;
      end loop;
      assert r(10 downto 8) = "000"
        report "abstract command failed, cmderr /= 0, ABSTRACTCS=0x"
               & to_hstring(r) severity failure;
    end procedure wait_cmd_done;

    variable polls : natural;
  begin
    rst_n <= '0';
    wait for 5 * CLK_PERIOD;
    rst_n <= '1';
    wait for 2 * CLK_PERIOD;

    ----------------------------------------------------------------------
    -- Preamble: activate DM, halt the hart (Stage-2 handshake).
    ----------------------------------------------------------------------
    dmi_write(A_DMCONTROL, x"00000001");  -- dmactive=1
    dmi_write(A_DMCONTROL, x"80000001");  -- haltreq=1, dmactive=1
    polls := 0;
    loop
      dmi_read(A_DMSTATUS, rd);
      exit when rd(9) = '1';              -- allhalted
      polls := polls + 1;
      assert polls < 25
        report "PREAMBLE FAIL: hart did not halt" severity failure;
    end loop;

    ----------------------------------------------------------------------
    -- CHECK1: DATA0 -> COMMAND write x5 (aarsize=2) -> regfile x5.
    ----------------------------------------------------------------------
    dmi_write(A_DATA0, x"CAFEBABE");
    dmi_read(A_DATA0, rd);
    assert rd = x"CAFEBABE"
      report "CHECK1 FAIL: DATA0 round-trip broke, got 0x" & to_hstring(rd)
      severity failure;
    -- cmdtype=0, aarsize=2, transfer=1, write=1, regno=0x1005 (x5)
    dmi_write(A_COMMAND, x"00231005");
    wait_cmd_done;
    wait for CLK_PERIOD;
    assert regs(5) = x"00000000CAFEBABE"
      report "CHECK1 FAIL: x5 /= zero-extended 0xCAFEBABE, got 0x"
             & to_hstring(regs(5)) severity failure;
    report "CHECK1 PASS: DATA0 -> abstract write x5 (aarsize=2), "
           & "zero-extended into 64-bit GPR" severity note;

    ----------------------------------------------------------------------
    -- CHECK2: COMMAND read x5 (aarsize=2) -> DATA0.
    ----------------------------------------------------------------------
    dmi_write(A_DATA0, x"00000000");      -- clobber before readback
    -- cmdtype=0, aarsize=2, transfer=1, write=0, regno=0x1005 (x5)
    dmi_write(A_COMMAND, x"00221005");
    wait_cmd_done;
    dmi_read(A_DATA0, rd);
    assert rd = x"CAFEBABE"
      report "CHECK2 FAIL: DATA0 /= 0xCAFEBABE after read x5, got 0x"
             & to_hstring(rd) severity failure;
    report "CHECK2 PASS: abstract read x5 (aarsize=2) -> DATA0 == 0xCAFEBABE"
      severity note;

    ----------------------------------------------------------------------
    -- CHECK3: 64-bit write + readback of x6 (aarsize=3, DATA0+DATA1).
    ----------------------------------------------------------------------
    dmi_write(A_DATA0, x"11223344");
    dmi_write(A_DATA1, x"55667788");
    -- cmdtype=0, aarsize=3, transfer=1, write=1, regno=0x1006 (x6)
    dmi_write(A_COMMAND, x"00331006");
    wait_cmd_done;
    wait for CLK_PERIOD;
    assert regs(6) = x"5566778811223344"
      report "CHECK3 FAIL: x6 /= 0x5566778811223344, got 0x"
             & to_hstring(regs(6)) severity failure;
    dmi_write(A_DATA0, x"00000000");
    dmi_write(A_DATA1, x"00000000");
    -- cmdtype=0, aarsize=3, transfer=1, write=0, regno=0x1006 (x6)
    dmi_write(A_COMMAND, x"00321006");
    wait_cmd_done;
    dmi_read(A_DATA0, rd);
    assert rd = x"11223344"
      report "CHECK3 FAIL: DATA0 /= low half, got 0x" & to_hstring(rd)
      severity failure;
    dmi_read(A_DATA1, rd);
    assert rd = x"55667788"
      report "CHECK3 FAIL: DATA1 /= high half, got 0x" & to_hstring(rd)
      severity failure;
    report "CHECK3 PASS: 64-bit abstract write+read x6 via DATA0+DATA1"
      severity note;

    ----------------------------------------------------------------------
    -- CHECK4: running hart -> COMMAND fails with cmderr=4; W1C clears.
    ----------------------------------------------------------------------
    dmi_write(A_DMCONTROL, x"40000001");  -- resumereq=1, haltreq=0
    polls := 0;
    loop
      dmi_read(A_DMSTATUS, rd);
      exit when rd(17) = '1' and rd(11) = '1';  -- allresumeack + allrunning
      polls := polls + 1;
      assert polls < 25
        report "CHECK4 FAIL: hart did not resume" severity failure;
    end loop;
    dmi_write(A_COMMAND, x"00221005");    -- valid command, but running
    dmi_read(A_ABSTRACTCS, rd);
    assert rd(10 downto 8) = "100"
      report "CHECK4 FAIL: cmderr /= 4 for COMMAND while running, "
             & "ABSTRACTCS=0x" & to_hstring(rd) severity failure;
    dmi_write(A_ABSTRACTCS, x"00000700"); -- W1C
    dmi_read(A_ABSTRACTCS, rd);
    assert rd(10 downto 8) = "000"
      report "CHECK4 FAIL: cmderr not cleared by W1C, ABSTRACTCS=0x"
             & to_hstring(rd) severity failure;
    report "CHECK4 PASS: COMMAND while running -> cmderr=4; W1C clears"
      severity note;

    ----------------------------------------------------------------------
    -- CHECK5: bad regno 0x2000 -> cmderr=2 (not supported); W1C clears.
    ----------------------------------------------------------------------
    dmi_write(A_DMCONTROL, x"80000001");  -- re-halt
    polls := 0;
    loop
      dmi_read(A_DMSTATUS, rd);
      exit when rd(9) = '1';
      polls := polls + 1;
      assert polls < 25
        report "CHECK5 FAIL: hart did not re-halt" severity failure;
    end loop;
    -- cmdtype=0, aarsize=2, transfer=1, write=1, regno=0x2000 (CSR range)
    dmi_write(A_COMMAND, x"00232000");
    dmi_read(A_ABSTRACTCS, rd);
    assert rd(10 downto 8) = "010"
      report "CHECK5 FAIL: cmderr /= 2 for regno 0x2000, ABSTRACTCS=0x"
             & to_hstring(rd) severity failure;
    dmi_write(A_ABSTRACTCS, x"00000700"); -- W1C
    dmi_read(A_ABSTRACTCS, rd);
    assert rd(10 downto 8) = "000"
      report "CHECK5 FAIL: cmderr not cleared by W1C, ABSTRACTCS=0x"
             & to_hstring(rd) severity failure;
    report "CHECK5 PASS: unsupported regno 0x2000 -> cmderr=2; W1C clears"
      severity note;

    ----------------------------------------------------------------------
    -- CHECK6: Stage-2 regression (in-bench): halt/resume handshake was
    -- exercised above; ndmreset -> havereset, ackhavereset clears.
    ----------------------------------------------------------------------
    dmi_write(A_DMCONTROL, x"00000003");  -- ndmreset=1, dmactive=1
    dmi_write(A_DMCONTROL, x"00000001");  -- ndmreset=0
    dmi_read(A_DMSTATUS, rd);
    assert rd(18) = '1' and rd(19) = '1'
      report "CHECK6 FAIL: havereset not set after ndmreset pulse, "
             & "DMSTATUS=0x" & to_hstring(rd) severity failure;
    dmi_write(A_DMCONTROL, x"10000001");  -- ackhavereset=1
    dmi_read(A_DMSTATUS, rd);
    assert rd(18) = '0' and rd(19) = '0'
      report "CHECK6 FAIL: havereset not cleared by ackhavereset, "
             & "DMSTATUS=0x" & to_hstring(rd) severity failure;
    report "CHECK6 PASS: Stage-2 DM semantics intact "
           & "(halt/resume + havereset handshake)" severity note;

    ----------------------------------------------------------------------
    -- CHECK7: Stage-1 regression (in-bench): dmi_bus scratch round-trips
    -- through the same bus that now routes 0x04..0x0B to the DM. Scratch
    -- is 0x00..0x03 (Stage-4 shrink); 0x04 is DATA0 (exercised above).
    ----------------------------------------------------------------------
    dmi_write(A_SCRATCH3, x"DEADBEEF");
    dmi_read(A_SCRATCH3, rd);
    assert rd = x"DEADBEEF"
      report "CHECK7 FAIL: scratch 0x03 round-trip broke, got 0x"
             & to_hstring(rd) severity failure;
    dmi_write(A_SCRATCH0, x"12345678");
    dmi_read(A_SCRATCH0, rd);
    assert rd = x"12345678"
      report "CHECK7 FAIL: scratch 0x00 round-trip broke, got 0x"
             & to_hstring(rd) severity failure;
    report "CHECK7 PASS: dmi_bus scratch regfile intact (0x00, 0x03)"
      severity note;

    report "JTAG STAGE3 PASS" severity note;
    finish;
  end process stim;

end architecture sim;
