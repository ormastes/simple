-- uart_bscan_log.vhd — always-on BSCANE2 (USER4) UART-log tap for boards with
-- NO debug module and NO UART adapter wired (rv64 SoC, 2026-07-24 campaign).
--
-- PURPOSE: give the host a board-origin evidence channel for a long soak run
-- when there is no serial cable: every UART byte the core's soft-UART would
-- have transmitted is captured in a shift window here, and the LATEST 16 bytes
-- + a running byte counter are read back over the SAME FT4232H JTAG chain used
-- to program the board, via a Xilinx BSCANE2 USER4 tap. This is a read-only
-- OBSERVATION tap — it adds no debug semantics (no halt/step/DM), unlike the
-- jtag_debug_chain path; see doc/07_guide/hardware/fpga/simple_riscv_jtag_debugging.md.
--
-- DATA (144 bits total, captured MSB-aligned so byte_cnt lands at the high end
-- of the DR and last_bytes fills the rest):
--   capture_data(143 downto 128) = byte_cnt(15 downto 0)   -- total bytes seen
--   capture_data(127 downto   0) = last_bytes               -- newest 16 bytes,
--     shifted so the MOST RECENT byte occupies bits (7 downto 0) (it enters at
--     the LSB end, `last_bytes(119 downto 0) & debug_uart_byte`) and the OLDEST
--     of the 16 kept bytes sits at bits (127 downto 120), dropped on the next
--     push.
--
-- CLOCK DOMAINS: byte_cnt/last_bytes are core-clk-domain registers (driven by
-- debug_uart_valid pulses from the RISC-V core's soft-UART). The BSCANE2 DR
-- shift register is clocked by DRCK (the JTAG-side clock BSCANE2 hands to
-- fabric per Xilinx UG470) and samples the core-clk-domain bytes/counter
-- straight into the CAPTURE stage with no synchronizer — the byte stream is
-- slow (about one byte per several seconds at soak progress-marker intervals),
-- so a mid-capture torn read is exceedingly unlikely, and this is quasi-static
-- sampling per the plan: the host is expected to read twice and require two
-- consecutive identical reads before trusting a value.
--
-- UPDATE/TDI are ignored (read-only tap, mirrors debug_registers-style status
-- shift regs); RESET/RUNTEST are not needed either.
--
-- Instantiated from soc_top_rv64.vhd (real unisim.vcomponents.BSCANE2 primitive
-- lives there, JTAG_CHAIN => 4, mirroring soc_top_rv32.vhd's gen_debug arm).
-- This entity itself uses NO unisim primitives, so it GHDL-analyzes/elaborates
-- standalone (see tb_uart_bscan_log.vhd, which drives bsc_* directly the way a
-- real BSCANE2 would, mirroring tb_bscane2_bridge's use of bscane2_stub).

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

entity uart_bscan_log is
  port (
    clk    : in std_logic;   -- core-clk domain (data source)
    rst_n  : in std_logic;

    -- Data source: pulses once per UART byte the core's soft-UART emits.
    debug_uart_valid : in std_logic;
    debug_uart_byte  : in std_logic_vector(7 downto 0);

    -- BSCANE2 USER4 data-register interface (real primitive lives in the
    -- instantiating top; see bscane2_tap_bridge.vhd for the same port shape).
    bsc_sel     : in  std_logic;
    bsc_drck    : in  std_logic;
    bsc_capture : in  std_logic;
    bsc_shift   : in  std_logic;
    bsc_update  : in  std_logic;  -- unused (read-only tap)
    bsc_tdi     : in  std_logic;  -- unused (read-only tap)
    bsc_tdo     : out std_logic
  );
end entity uart_bscan_log;

architecture rtl of uart_bscan_log is
  signal byte_cnt   : unsigned(15 downto 0) := (others => '0');
  signal last_bytes : std_logic_vector(127 downto 0) := (others => '0');

  signal shreg : std_logic_vector(143 downto 0) := (others => '0');
begin
  -- Core-clk domain: accumulate the UART byte stream into a 16-byte window +
  -- running counter. New bytes enter at the bottom (bits 7 downto 0); the
  -- oldest kept byte (bits 127 downto 120) is dropped on the next push.
  accumulate : process (clk)
  begin
    if rising_edge(clk) then
      if rst_n = '0' then
        byte_cnt   <= (others => '0');
        last_bytes <= (others => '0');
      elsif debug_uart_valid = '1' then
        last_bytes <= last_bytes(119 downto 0) & debug_uart_byte;
        byte_cnt   <= byte_cnt + 1;
      end if;
    end if;
  end process accumulate;

  -- BSCANE2 DR domain: on CAPTURE, load {byte_cnt, last_bytes} (quasi-static
  -- sample of the core-clk registers, no synchronizer — see header). On
  -- SHIFT, shift the register right one bit per DRCK edge and present the
  -- current LSB on TDO, so a full DR scan reads the 144 bits out LSB-first.
  dr_shift : process (bsc_drck)
  begin
    if rising_edge(bsc_drck) then
      if bsc_sel = '1' then
        if bsc_capture = '1' then
          shreg <= std_logic_vector(byte_cnt) & last_bytes;
        elsif bsc_shift = '1' then
          shreg <= '0' & shreg(143 downto 1);
        end if;
      end if;
    end if;
  end process dr_shift;

  bsc_tdo <= shreg(0);
end architecture rtl;
