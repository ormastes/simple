-- tb_uart_bscan_log.vhd — GHDL self-consistency proof of uart_bscan_log:
-- pumps fake debug_uart_valid/byte pulses on the clk domain (mimicking the
-- rv64 core's soft-UART), then drives the bsc_* BSCANE2 DR interface directly
-- (mirroring how tb_bscane2_bridge drives bscane2_stub's v_* signals) and
-- checks the 144-bit CAPTURE/SHIFT DR read-back equals {byte_cnt, last_bytes}
-- computed by an independent tb-side model of the same push sequence.
--
-- Prints "UART_BSCAN_LOG SELF-CONSISTENT PASS" only if every sampled bit
-- matches the expected value.

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use std.env.all;

entity tb_uart_bscan_log is
end entity tb_uart_bscan_log;

architecture sim of tb_uart_bscan_log is
  signal clk   : std_logic := '0';
  signal rst_n : std_logic := '0';
  signal duv   : std_logic := '0';
  signal dub   : std_logic_vector(7 downto 0) := (others => '0');

  signal bsc_sel     : std_logic := '0';
  signal bsc_drck    : std_logic := '0';
  signal bsc_capture : std_logic := '0';
  signal bsc_shift   : std_logic := '0';
  signal bsc_update  : std_logic := '0';
  signal bsc_tdi     : std_logic := '0';
  signal bsc_tdo     : std_logic;

  signal readback : std_logic_vector(143 downto 0) := (others => '0');
  signal fail_seen : boolean := false;
begin
  clk <= not clk after 5 ns;

  dut : entity work.uart_bscan_log
    port map (
      clk => clk, rst_n => rst_n,
      debug_uart_valid => duv, debug_uart_byte => dub,
      bsc_sel => bsc_sel, bsc_drck => bsc_drck, bsc_capture => bsc_capture,
      bsc_shift => bsc_shift, bsc_update => bsc_update, bsc_tdi => bsc_tdi,
      bsc_tdo => bsc_tdo);

  stim : process
    -- Push one byte through the debug_uart_valid pulse on the clk domain,
    -- updating the tb-side model of {byte_cnt, last_bytes} identically to
    -- the DUT's accumulate process.
    procedure push_byte(b : std_logic_vector(7 downto 0);
                         variable cnt   : inout unsigned(15 downto 0);
                         variable win   : inout std_logic_vector(127 downto 0)) is
    begin
      wait until rising_edge(clk);
      duv <= '1'; dub <= b;
      wait until rising_edge(clk);
      duv <= '0';
      cnt := cnt + 1;
      win := win(119 downto 0) & b;
      wait for 20 ns;
    end procedure;

    -- One BSCANE2 DRCK pulse (JTAG-side clock is not free-running).
    procedure drck_pulse is
    begin
      wait for 20 ns;
      bsc_drck <= '1';
      wait for 20 ns;
      bsc_drck <= '0';
      wait for 20 ns;
    end procedure;

    -- CAPTURE + full 144-bit SHIFT-out of the DR, LSB-first, into `readback`.
    procedure read_dr is
    begin
      bsc_sel <= '1';
      bsc_capture <= '1';
      drck_pulse;                        -- captures {byte_cnt, last_bytes}
      bsc_capture <= '0';
      bsc_shift <= '1';
      for i in 0 to 143 loop
        readback(i) <= bsc_tdo;          -- bit i valid before this step
        drck_pulse;                       -- shift right; reveals bit i+1
      end loop;
      bsc_shift <= '0';
      bsc_sel <= '0';
      wait for 20 ns;
    end procedure;

    variable exp_cnt : unsigned(15 downto 0) := (others => '0');
    variable exp_win : std_logic_vector(127 downto 0) := (others => '0');
    variable exp_dr  : std_logic_vector(143 downto 0);
  begin
    rst_n <= '0';
    wait for 50 ns;
    rst_n <= '1';
    wait for 20 ns;

    -- Round 1: push 3 bytes ('P','D','O' -- arbitrary), then read back.
    push_byte(x"50", exp_cnt, exp_win);
    push_byte(x"44", exp_cnt, exp_win);
    push_byte(x"4F", exp_cnt, exp_win);
    wait for 30 ns;

    read_dr;
    wait for 10 ns;
    exp_dr := std_logic_vector(exp_cnt) & exp_win;
    assert readback = exp_dr
      report "UART_BSCAN_LOG FAIL round1: readback=0x" & to_hstring(readback)
             & " expected=0x" & to_hstring(exp_dr) severity error;
    if readback /= exp_dr then fail_seen <= true; end if;
    report "round1 byte_cnt=" & integer'image(to_integer(exp_cnt)) severity note;

    -- Round 2: push 20 more bytes (exceeds the 16-byte window -> exercises
    -- the drop-oldest path), then read back again; byte_cnt must have grown
    -- monotonically and the window must hold exactly the last 16 bytes.
    for k in 0 to 19 loop
      push_byte(std_logic_vector(to_unsigned(k, 8)), exp_cnt, exp_win);
    end loop;
    wait for 30 ns;

    read_dr;
    wait for 10 ns;
    exp_dr := std_logic_vector(exp_cnt) & exp_win;
    assert readback = exp_dr
      report "UART_BSCAN_LOG FAIL round2: readback=0x" & to_hstring(readback)
             & " expected=0x" & to_hstring(exp_dr) severity error;
    if readback /= exp_dr then fail_seen <= true; end if;
    report "round2 byte_cnt=" & integer'image(to_integer(exp_cnt)) severity note;

    -- Double-read requirement sanity: reading again with no new pushes must
    -- return the SAME value (quasi-static consistency the host relies on).
    read_dr;
    wait for 10 ns;
    assert readback = exp_dr
      report "UART_BSCAN_LOG FAIL double-read: value changed with no new bytes"
      severity error;
    if readback /= exp_dr then fail_seen <= true; end if;

    if fail_seen then
      report "UART_BSCAN_LOG SELF-CONSISTENT: FAIL" severity failure;
    else
      report "UART_BSCAN_LOG SELF-CONSISTENT PASS: byte_cnt=" & integer'image(to_integer(exp_cnt))
             & " last_bytes=0x" & to_hstring(exp_win) severity note;
    end if;
    finish;
  end process;
end architecture sim;
