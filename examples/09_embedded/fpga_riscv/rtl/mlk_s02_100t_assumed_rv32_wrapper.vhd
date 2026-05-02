-- Assumption-only MLK-S02-100T RV32 wrapper.
--
-- WARNING:
-- - non-authoritative
-- - not based on vendor HDL or schematic
-- - memory is tied off, so Linux boot is not expected to work
-- - intended only for provisional synth/place/route experiments

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use work.simple_rv32i_core_pkg.all;

entity mlk_s02_100t_assumed_rv32_wrapper is
    port (
        clk25   : in  std_logic;
        rst_n   : in  std_logic;
        uart_tx : out std_logic;
        uart_rx : in  std_logic;
        led     : out std_logic_vector(7 downto 0);
        btn     : in  std_logic_vector(3 downto 0)
    );
end entity mlk_s02_100t_assumed_rv32_wrapper;

architecture rtl of mlk_s02_100t_assumed_rv32_wrapper is
    signal imem_addr_s  : xword_t;
    signal dmem_addr_s  : xword_t;
    signal dmem_wdata_s : xword_t;
    signal dmem_we_s    : std_logic;
    signal dmem_re_s    : std_logic;
    signal dmem_width_s : std_logic_vector(1 downto 0);
    signal dmem_wstrb_s : std_logic_vector((XLEN / 8) - 1 downto 0);
    signal debug_pc_s   : xword_t;
    signal semi_trigger_s : std_logic;
    signal semi_op_s    : xword_t;
    signal semi_param_s : xword_t;
    signal trap_s       : std_logic;
    signal halt_s       : std_logic;
begin
    core_i : entity work.simple_rv32gc_core
        port map (
            clk          => clk25,
            reset_n      => rst_n,
            imem_addr    => imem_addr_s,
            imem_rdata   => (others => '0'),
            dmem_addr    => dmem_addr_s,
            dmem_wdata   => dmem_wdata_s,
            dmem_rdata   => (others => '0'),
            dmem_we      => dmem_we_s,
            dmem_re      => dmem_re_s,
            dmem_width   => dmem_width_s,
            dmem_wstrb   => dmem_wstrb_s,
            irq_software => '0',
            irq_timer    => '0',
            irq_external => '0',
            debug_pc     => debug_pc_s,
            semi_trigger => semi_trigger_s,
            semi_op      => semi_op_s,
            semi_param   => semi_param_s,
            trap         => trap_s,
            halt         => halt_s
        );

    uart_tx <= '1';
    led(0) <= trap_s;
    led(1) <= halt_s;
    led(2) <= semi_trigger_s;
    led(3) <= debug_pc_s(2);
    led(4) <= debug_pc_s(3);
    led(5) <= btn(0);
    led(6) <= btn(1);
    led(7) <= uart_rx;
end architecture rtl;
