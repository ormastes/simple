-- bscane2_stub.vhd — Lane B: GHDL sim model of the Xilinx BSCANE2 primitive.
--
-- The real BSCANE2 (UltraScale/UltraScale+) is a hard macro that taps the FPGA's
-- dedicated JTAG TAP and exposes a USER<n> instruction's data-register strobes
-- to fabric. GHDL cannot analyze the unisim primitive, so this stub reproduces
-- its fabric-facing port contract (same output names) and lets a testbench act
-- as the JTAG host by driving the `v_*` virtual-JTAG inputs. It is used ONLY in
-- simulation (tb_bscane2_bridge); soc_top_rv32.vhd instantiates the real
-- unisim.vcomponents.BSCANE2 in synthesis, guarded by G_DEBUG_JTAG.
--
-- Only the strobes bscane2_tap_bridge consumes are modelled
-- (SEL/DRCK/CAPTURE/SHIFT/UPDATE/TDI + TDO); RESET/RUNTEST/TCK/TMS are provided
-- for port-name fidelity and driven from the virtual host too.

library ieee;
use ieee.std_logic_1164.all;

entity bscane2_stub is
  generic (
    JTAG_CHAIN : integer := 1   -- which USER instruction (1..4); fidelity only
  );
  port (
    -- Fabric-facing outputs (mirror the real BSCANE2 output ports).
    CAPTURE : out std_logic;
    DRCK    : out std_logic;
    RESET   : out std_logic;
    RUNTEST : out std_logic;
    SEL     : out std_logic;
    SHIFT   : out std_logic;
    TCK     : out std_logic;
    TMS     : out std_logic;
    UPDATE  : out std_logic;
    TDI     : out std_logic;
    TDO     : in  std_logic;

    -- Virtual JTAG host drive (sim only — NOT present on the real primitive).
    v_capture : in std_logic := '0';
    v_drck    : in std_logic := '0';
    v_reset   : in std_logic := '0';
    v_runtest : in std_logic := '0';
    v_sel     : in std_logic := '0';
    v_shift   : in std_logic := '0';
    v_tck     : in std_logic := '0';
    v_tms     : in std_logic := '0';
    v_update  : in std_logic := '0';
    v_tdi     : in std_logic := '0'
  );
end entity bscane2_stub;

architecture rtl of bscane2_stub is
begin
  CAPTURE <= v_capture;
  DRCK    <= v_drck;
  RESET   <= v_reset;
  RUNTEST <= v_runtest;
  SEL     <= v_sel;
  SHIFT   <= v_shift;
  TCK     <= v_tck;
  TMS     <= v_tms;
  UPDATE  <= v_update;
  TDI     <= v_tdi;
  -- TDO is an input from fabric; the host samples it externally.
end architecture rtl;
