-- tb_openocd_bitbang.vhd — Stage-5 OpenOCD attach harness: a remote_bitbang
-- TCP server (via VHPIDIRECT C glue, openocd_bitbang_glue.c) driving the
-- REAL full stack: jtag_tap -> riscv_dtm -> dmi_bus -> riscv_debug_module
-- (abstract GPR + debug CSRs + SBA) -> sba_test_mem, plus the same fake
-- hart / GPR models used by tb_debug_csrs.
--
-- This is NOT part of the regression gate (it blocks on a TCP accept).
-- Full attach procedure + verified transcript: openocd_attach.md (same dir).
--
-- Build/run (ghdl-mcode, the Ubuntu default, cannot -Wl-link objects; the
-- foreign strings below therefore name the shared lib "bb_glue.so", found
-- via LD_LIBRARY_PATH / dlopen search):
--   1) cc -shared -fPIC -o bb_glue.so openocd_bitbang_glue.c
--      ghdl -a --std=08 <rtl + this file>
--      LD_LIBRARY_PATH=$PWD ghdl -r --std=08 tb_openocd_bitbang
--        (blocks: "[bitbang] listening on 127.0.0.1:9999")
--   2) openocd -f openocd_riscv_sim.cfg -c init ... -c shutdown
--
-- remote_bitbang protocol handled: '0'..'7' write tck/tms/tdi, 'R' read
-- TDO, 'r'/'s'/'t'/'u' trst/srst, 'B'/'b' LED blink (ignored), 'Q' quit.
-- The simulation finishes on 'Q' or when OpenOCD disconnects.

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use std.env.all;

entity tb_openocd_bitbang is
  generic (
    TCP_PORT : integer := 9999
  );
end entity tb_openocd_bitbang;

architecture sim of tb_openocd_bitbang is

  -- VHPIDIRECT bindings (bodies are placeholders, never executed).
  function bb_init(port_v : integer) return integer is
  begin
    report "bb_init not linked (VHPIDIRECT)" severity failure;
    return -1;
  end function bb_init;
  attribute foreign of bb_init : function is "VHPIDIRECT bb_glue.so bb_init";

  impure function bb_next return integer is
  begin
    report "bb_next not linked (VHPIDIRECT)" severity failure;
    return -1;
  end function bb_next;
  attribute foreign of bb_next : function is "VHPIDIRECT bb_glue.so bb_next";

  procedure bb_send(bit_v : integer) is
  begin
    report "bb_send not linked (VHPIDIRECT)" severity failure;
  end procedure bb_send;
  attribute foreign of bb_send : procedure is "VHPIDIRECT bb_glue.so bb_send";

  constant EXPECTED_IDCODE : std_logic_vector(31 downto 0) := x"15350067";

  signal tck    : std_logic := '0';
  signal tms    : std_logic := '0';
  signal tdi    : std_logic := '0';
  signal trst_n : std_logic := '1';
  signal tdo    : std_logic;
  signal tlr_o  : std_logic;

  signal sel_dtmcs, sel_dmi              : std_logic;
  signal capture_en, shift_en, update_en : std_logic;
  signal dr_tdi                          : std_logic;
  signal dtmcs_tdo, dmi_tdo              : std_logic;

  signal dmi_valid : std_logic;
  signal dmi_addr  : std_logic_vector(6 downto 0);
  signal dmi_wdata : std_logic_vector(31 downto 0);
  signal dmi_op    : std_logic_vector(1 downto 0);
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

  signal haltreq_s, resumereq_s, ndmreset_s : std_logic;
  signal halted_s, running_s                : std_logic;
  signal hart_halted : std_logic := '0';
  signal hart_pc     : std_logic_vector(63 downto 0) := x"0000000080000000";
  signal dpc_s       : std_logic_vector(63 downto 0);
  signal step_s      : std_logic;

  signal gpr_re_s    : std_logic;
  signal gpr_we_s    : std_logic;
  signal gpr_regno_s : std_logic_vector(4 downto 0);
  signal gpr_wdata_s : std_logic_vector(63 downto 0);
  signal gpr_rdata_s : std_logic_vector(63 downto 0) := (others => '0');
  signal gpr_ack_s   : std_logic := '0';

  type regfile_t is array (0 to 31) of std_logic_vector(63 downto 0);
  signal regs : regfile_t := (others => (others => '0'));

  signal sb_re    : std_logic;
  signal sb_we    : std_logic;
  signal sb_addr  : std_logic_vector(63 downto 0);
  signal sb_wdata : std_logic_vector(63 downto 0);
  signal sb_size  : std_logic_vector(1 downto 0);
  signal sb_rdata : std_logic_vector(63 downto 0);
  signal sb_ack   : std_logic;
  signal sb_err   : std_logic;

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
      valid => dmi_valid, addr => dmi_addr, wdata => dmi_wdata, op => dmi_op,
      rdata => dmi_rdata, resp => dmi_resp, ready => dmi_ready,
      dm_valid => dm_valid, dm_addr => dm_addr,
      dm_wdata => dm_wdata, dm_op => dm_op,
      dm_rdata => dm_rdata, dm_resp => dm_resp, dm_ready => dm_ready);

  u_dm : entity work.riscv_debug_module
    port map (
      clk => tck, rst_n => trst_n,
      dmi_valid => dm_valid, dmi_addr => dm_addr,
      dmi_wdata => dm_wdata, dmi_op => dm_op,
      dmi_rdata => dm_rdata, dmi_resp => dm_resp, dmi_ready => dm_ready,
      haltreq_o => haltreq_s, resumereq_o => resumereq_s,
      ndmreset_o => ndmreset_s,
      halted_i => halted_s, running_i => running_s,
      gpr_re_o => gpr_re_s, gpr_we_o => gpr_we_s,
      gpr_regno_o => gpr_regno_s, gpr_wdata_o => gpr_wdata_s,
      gpr_rdata_i => gpr_rdata_s, gpr_ack_i => gpr_ack_s,
      pc_i => hart_pc, prv_i => "11", ebreak_i => '0',
      dpc_o => dpc_s, step_o => step_s,
      sb_re_o => sb_re, sb_we_o => sb_we,
      sb_addr_o => sb_addr, sb_wdata_o => sb_wdata, sb_size_o => sb_size,
      sb_rdata_i => sb_rdata, sb_ack_i => sb_ack, sb_err_i => sb_err);

  u_mem : entity work.sba_test_mem
    generic map (ACK_DELAY => 2)
    port map (
      clk => tck, rst_n => trst_n,
      sb_re_i => sb_re, sb_we_i => sb_we,
      sb_addr_i => sb_addr, sb_wdata_i => sb_wdata, sb_size_i => sb_size,
      sb_rdata_o => sb_rdata, sb_ack_o => sb_ack, sb_err_o => sb_err);

  -- Fake hart (same model as tb_debug_csrs): free-running pc, halts 3 tck
  -- after haltreq, resumes at dpc 3 tck after resumereq, single-steps when
  -- dcsr.step is set.
  fake_hart : process (tck, trst_n)
    variable cnt      : natural := 0;
    variable step_cnt : natural := 0;
    variable stepping : boolean := false;
  begin
    if trst_n = '0' then
      hart_halted <= '0';
      hart_pc     <= x"0000000080000000";
      cnt := 0; step_cnt := 0; stepping := false;
    elsif rising_edge(tck) then
      if hart_halted = '1' then
        if resumereq_s = '1' then
          if cnt = 3 then
            cnt := 0;
            hart_halted <= '0';
            hart_pc     <= dpc_s;
            stepping    := (step_s = '1');
            step_cnt    := 0;
          else
            cnt := cnt + 1;
          end if;
        else
          cnt := 0;
        end if;
      else
        if stepping then
          if step_cnt = 1 then
            stepping := false;
            step_cnt := 0;
            hart_halted <= '1';
          else
            hart_pc  <= std_logic_vector(unsigned(hart_pc) + 4);
            step_cnt := step_cnt + 1;
          end if;
        elsif haltreq_s = '1' then
          if cnt = 3 then
            cnt := 0;
            hart_halted <= '1';
          else
            cnt := cnt + 1;
            hart_pc <= std_logic_vector(unsigned(hart_pc) + 4);
          end if;
        else
          cnt := 0;
          hart_pc <= std_logic_vector(unsigned(hart_pc) + 4);
        end if;
      end if;
    end if;
  end process fake_hart;

  halted_s  <= hart_halted;
  running_s <= not hart_halted;

  -- Fake 32 x 64-bit GPR regfile: ack after 2 tck of re/we held high.
  gpr_model : process (tck, trst_n)
    variable cnt : natural := 0;
  begin
    if trst_n = '0' then
      gpr_ack_s   <= '0';
      gpr_rdata_s <= (others => '0');
      cnt := 0;
    elsif rising_edge(tck) then
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

  -- remote_bitbang server loop.
  server : process
    variable rc : integer;
    variable c  : integer;
    variable v  : integer;
  begin
    rc := bb_init(TCP_PORT);
    assert rc = 0
      report "bb_init failed, rc=" & integer'image(rc) severity failure;
    loop
      c := bb_next;
      if c < 0 or c = character'pos('Q') then
        report "OpenOCD session ended (quit/disconnect)" severity note;
        finish;
      elsif c >= character'pos('0') and c <= character'pos('7') then
        v := c - character'pos('0');
        if (v mod 2) = 1 then tdi <= '1'; else tdi <= '0'; end if;
        if ((v / 2) mod 2) = 1 then tms <= '1'; else tms <= '0'; end if;
        if ((v / 4) mod 2) = 1 then tck <= '1'; else tck <= '0'; end if;
        wait for 5 ns;
      elsif c = character'pos('R') then
        if tdo = '1' then bb_send(1); else bb_send(0); end if;
      elsif c = character'pos('r') or c = character'pos('s') then
        trst_n <= '1';                 -- trst deasserted
        wait for 5 ns;
      elsif c = character'pos('t') or c = character'pos('u') then
        trst_n <= '0';                 -- trst asserted
        wait for 5 ns;
      end if;
      -- 'B'/'b' (blink) and anything else: ignored
    end loop;
  end process server;

end architecture sim;
