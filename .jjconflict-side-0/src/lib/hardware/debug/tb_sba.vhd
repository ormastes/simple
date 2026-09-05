-- tb_sba.vhd — GHDL testbench for Stage 5 System Bus Access.
--
-- Full stack under test: dmi_bus (0x38..0x3D forwarding) -> riscv_debug_module
-- -> debug_registers SBA engine -> sba_test_mem (ACK_DELAY=8 so sbbusy has a
-- real window; every access requires polling like on real silicon).
--
-- Acceptance checks (each backed by `assert ... severity failure`):
--   1. SBCS reset value: sbversion=1, sbaccess=2, sbasize=64,
--      sbaccess32/64=1 (exact value 0x2004080C).
--   2. sbreadonaddr, 64-bit: write SBADDRESS0=0x10 -> SBDATA0/SBDATA1 ==
--      mem word 2 (0xA5A5000000020002).
--   3. 32-bit bus write via SBDATA0 -> memory updated (verified by SBA
--      read-back of both halves of the word).
--   4. sbautoincrement + sbreadondata, 64-bit: two consecutive SBDATA0
--      reads return mem[i] then mem[i+1]; SBADDRESS0 shows the increments.
--   5. Errors: out-of-range address -> sberror=2, W1C clears; unsupported
--      sbaccess=1 -> sberror=4 (no bus access), W1C clears; while sberror
--      is set no new access starts.
--   6. Busy: SBDATA0 write while sbbusy=1 -> sbbusyerror sticky, write
--      dropped (memory intact), W1C clears, normal operation resumes.
--   7. (Run-gate) Stage 1-4 testbenches still pass unmodified logic.
--
-- Prints "JTAG STAGE5 PASS" only if every assert held.

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use std.env.all;

entity tb_sba is
end entity tb_sba;

architecture sim of tb_sba is

  constant CLK_PERIOD : time := 10 ns;

  signal clk   : std_logic := '0';
  signal rst_n : std_logic := '0';

  signal dmi_valid : std_logic := '0';
  signal dmi_addr  : std_logic_vector(6 downto 0) := (others => '0');
  signal dmi_wdata : std_logic_vector(31 downto 0) := (others => '0');
  signal dmi_op    : std_logic_vector(1 downto 0) := "00";
  signal dmi_rdata : std_logic_vector(31 downto 0);
  signal dmi_resp  : std_logic_vector(1 downto 0);
  signal dmi_ready : std_logic;

  signal dm_valid : std_logic;
  signal dm_addr  : std_logic_vector(6 downto 0);
  signal dm_wdata : std_logic_vector(31 downto 0);
  signal dm_op    : std_logic_vector(1 downto 0);
  signal dm_rdata : std_logic_vector(31 downto 0);
  signal dm_resp  : std_logic_vector(1 downto 0);
  signal dm_ready : std_logic;

  signal sb_re    : std_logic;
  signal sb_we    : std_logic;
  signal sb_addr  : std_logic_vector(63 downto 0);
  signal sb_wdata : std_logic_vector(63 downto 0);
  signal sb_size  : std_logic_vector(1 downto 0);
  signal sb_rdata : std_logic_vector(63 downto 0);
  signal sb_ack   : std_logic;
  signal sb_err   : std_logic;

  constant A_DMCONTROL  : std_logic_vector(6 downto 0) := "0010000";  -- 0x10
  constant A_SBCS       : std_logic_vector(6 downto 0) := "0111000";  -- 0x38
  constant A_SBADDRESS0 : std_logic_vector(6 downto 0) := "0111001";  -- 0x39
  constant A_SBADDRESS1 : std_logic_vector(6 downto 0) := "0111010";  -- 0x3A
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

    -- One DMI transaction through dmi_bus (same harness as tb_debug_csrs).
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
    procedure wait_sb_done(variable sbcs : out std_logic_vector(31 downto 0)) is
      variable r     : std_logic_vector(31 downto 0);
      variable polls : natural := 0;
    begin
      loop
        dmi_read(A_SBCS, r);
        exit when r(21) = '0';
        polls := polls + 1;
        assert polls < 25
          report "SBA access stuck busy, SBCS=0x" & to_hstring(r)
          severity failure;
      end loop;
      sbcs := r;
    end procedure wait_sb_done;

    variable sbcs : std_logic_vector(31 downto 0);
  begin
    rst_n <= '0';
    wait for 5 * CLK_PERIOD;
    rst_n <= '1';
    wait for 2 * CLK_PERIOD;

    -- Activate the DM (dmactive=1).
    dmi_write(A_DMCONTROL, x"00000001");
    dmi_read(A_DMCONTROL, rd);
    assert rd(0) = '1'
      report "dmactive did not read back 1" severity failure;

    ---------------------------------------------------------------------
    -- Check 1: SBCS reset/capability value.
    ---------------------------------------------------------------------
    dmi_read(A_SBCS, rd);
    assert rd = x"2004080C"
      report "CHECK1 FAIL: SBCS reset value, got 0x" & to_hstring(rd)
      severity failure;
    report "CHECK1 PASS: SBCS = 0x" & to_hstring(rd)
      & " (sbversion=1, sbaccess=2, sbasize=64, sbaccess32/64=1)"
      severity note;

    ---------------------------------------------------------------------
    -- Check 2: sbreadonaddr, 64-bit read of mem word 2 (addr 0x10).
    ---------------------------------------------------------------------
    dmi_write(A_SBCS, x"00160000");  -- sbreadonaddr=1, sbaccess=3 (64-bit)
    dmi_write(A_SBADDRESS0, x"00000010");
    wait_sb_done(sbcs);
    assert sbcs(14 downto 12) = "000" and sbcs(22) = '0'
      report "CHECK2 FAIL: unexpected sberror/sbbusyerror, SBCS=0x"
        & to_hstring(sbcs) severity failure;
    dmi_read(A_SBDATA0, rd);
    assert rd = x"00020002"
      report "CHECK2 FAIL: SBDATA0 /= mem[2] low, got 0x" & to_hstring(rd)
      severity failure;
    dmi_read(A_SBDATA1, rd);
    assert rd = x"A5A50000"
      report "CHECK2 FAIL: SBDATA1 /= mem[2] high, got 0x" & to_hstring(rd)
      severity failure;
    report "CHECK2 PASS: sbreadonaddr 64-bit read, mem[0x10] = 0xA5A50000_00020002"
      severity note;

    ---------------------------------------------------------------------
    -- Check 3: 32-bit bus write via SBDATA0, verified by SBA read-back.
    ---------------------------------------------------------------------
    dmi_write(A_SBCS, x"00040000");        -- sbaccess=2 (32-bit), no triggers
    dmi_write(A_SBADDRESS0, x"00000024");  -- word 4, high half
    dmi_write(A_SBDATA0, x"CAFEBABE");     -- bus write
    wait_sb_done(sbcs);
    assert sbcs(14 downto 12) = "000" and sbcs(22) = '0'
      report "CHECK3 FAIL: write flagged error, SBCS=0x" & to_hstring(sbcs)
      severity failure;
    dmi_write(A_SBCS, x"00140000");        -- sbreadonaddr=1, sbaccess=2
    dmi_write(A_SBADDRESS0, x"00000024");  -- read back written half
    wait_sb_done(sbcs);
    dmi_read(A_SBDATA0, rd);
    assert rd = x"CAFEBABE"
      report "CHECK3 FAIL: read-back of written word, got 0x" & to_hstring(rd)
      severity failure;
    dmi_write(A_SBADDRESS0, x"00000020");  -- low half must be untouched
    wait_sb_done(sbcs);
    dmi_read(A_SBDATA0, rd);
    assert rd = x"00040004"
      report "CHECK3 FAIL: neighbor half clobbered, got 0x" & to_hstring(rd)
      severity failure;
    report "CHECK3 PASS: 32-bit bus write landed (0xCAFEBABE @0x24), neighbor intact"
      severity note;

    ---------------------------------------------------------------------
    -- Check 4: sbautoincrement + sbreadondata, 64-bit.
    ---------------------------------------------------------------------
    -- sbreadonaddr=1, sbaccess=3, sbautoincrement=1, sbreadondata=1
    dmi_write(A_SBCS, x"00178000");
    dmi_write(A_SBADDRESS0, x"00000008");  -- read mem[1]; addr -> 0x10
    wait_sb_done(sbcs);
    dmi_read(A_SBDATA0, rd);               -- mem[1] low; triggers read @0x10
    assert rd = x"00010001"
      report "CHECK4 FAIL: first SBDATA0 /= mem[1] low, got 0x"
        & to_hstring(rd) severity failure;
    wait_sb_done(sbcs);
    dmi_read(A_SBDATA0, rd);               -- mem[2] low; triggers read @0x18
    assert rd = x"00020002"
      report "CHECK4 FAIL: second SBDATA0 /= mem[2] low, got 0x"
        & to_hstring(rd) severity failure;
    wait_sb_done(sbcs);
    dmi_write(A_SBCS, x"00060000");        -- stop triggers (sbaccess=3 only)
    dmi_read(A_SBADDRESS0, rd);
    assert rd = x"00000020"
      report "CHECK4 FAIL: SBADDRESS0 after 3 auto-increments, got 0x"
        & to_hstring(rd) severity failure;
    report "CHECK4 PASS: autoincrement + readondata streamed mem[1], mem[2]"
      severity note;

    ---------------------------------------------------------------------
    -- Check 5: sberror paths + W1C.
    ---------------------------------------------------------------------
    dmi_write(A_SBCS, x"00160000");        -- sbreadonaddr=1, sbaccess=3
    dmi_write(A_SBADDRESS0, x"00000400");  -- out of range (>= 0x200)
    wait_sb_done(sbcs);
    assert sbcs(14 downto 12) = "010"
      report "CHECK5 FAIL: out-of-range sberror /= 2, SBCS=0x"
        & to_hstring(sbcs) severity failure;
    -- While sberror is set, no new access may start.
    dmi_write(A_SBADDRESS0, x"00000008");
    dmi_read(A_SBCS, rd);
    assert rd(21) = '0' and rd(14 downto 12) = "010"
      report "CHECK5 FAIL: access started despite sberror, SBCS=0x"
        & to_hstring(rd) severity failure;
    dmi_write(A_SBCS, x"00167000");        -- W1C sberror, keep fields
    dmi_read(A_SBCS, rd);
    assert rd(14 downto 12) = "000"
      report "CHECK5 FAIL: sberror not cleared by W1C, SBCS=0x"
        & to_hstring(rd) severity failure;
    -- Unsupported sbaccess=1 (16-bit) -> sberror=4, no bus access.
    dmi_write(A_SBCS, x"00120000");        -- sbreadonaddr=1, sbaccess=1
    dmi_write(A_SBADDRESS0, x"00000008");
    dmi_read(A_SBCS, rd);
    assert rd(21) = '0' and rd(14 downto 12) = "100"
      report "CHECK5 FAIL: unsupported size sberror /= 4, SBCS=0x"
        & to_hstring(rd) severity failure;
    dmi_write(A_SBCS, x"00167000");        -- W1C, back to sbaccess=3+readonaddr
    dmi_read(A_SBCS, rd);
    assert rd(14 downto 12) = "000"
      report "CHECK5 FAIL: sberror=4 not cleared by W1C, SBCS=0x"
        & to_hstring(rd) severity failure;
    report "CHECK5 PASS: sberror=2 (bad address) and =4 (bad size), W1C clears"
      severity note;

    ---------------------------------------------------------------------
    -- Check 6: sbbusy window + sbbusyerror sticky + recovery.
    ---------------------------------------------------------------------
    dmi_write(A_SBADDRESS0, x"00000008");  -- slow read starts (ACK_DELAY=8)
    dmi_read(A_SBCS, rd);
    assert rd(21) = '1'
      report "CHECK6 FAIL: sbbusy not observed during slow access, SBCS=0x"
        & to_hstring(rd) severity failure;
    dmi_write(A_SBDATA0, x"12345678");     -- while busy: must be dropped
    wait_sb_done(sbcs);
    assert sbcs(22) = '1'
      report "CHECK6 FAIL: sbbusyerror not set by access-while-busy, SBCS=0x"
        & to_hstring(sbcs) severity failure;
    dmi_read(A_SBDATA0, rd);               -- readondata=0: no trigger
    assert rd = x"00010001"
      report "CHECK6 FAIL: in-flight read corrupted, SBDATA0=0x"
        & to_hstring(rd) severity failure;
    dmi_write(A_SBCS, x"00560000");        -- W1C sbbusyerror, keep fields
    dmi_read(A_SBCS, rd);
    assert rd(22) = '0'
      report "CHECK6 FAIL: sbbusyerror not cleared by W1C, SBCS=0x"
        & to_hstring(rd) severity failure;
    -- Dropped write must not have touched memory; normal operation resumes.
    dmi_write(A_SBADDRESS0, x"00000008");
    wait_sb_done(sbcs);
    dmi_read(A_SBDATA0, rd);
    assert rd = x"00010001"
      report "CHECK6 FAIL: dropped write corrupted memory, got 0x"
        & to_hstring(rd) severity failure;
    report "CHECK6 PASS: sbbusy observed, busy-write dropped + sbbusyerror W1C"
      severity note;

    ---------------------------------------------------------------------
    report "JTAG STAGE5 PASS" severity note;
    finish;
  end process;

end architecture sim;
