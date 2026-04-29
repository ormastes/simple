library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use work.simple_rv32i_core_pkg.all;

entity rv32i_core is
    generic (
        RESET_ADDR : std_logic_vector(31 downto 0) := x"80000000"
    );
    port (
        clk          : in  std_logic;
        reset_n      : in  std_logic;
        imem_addr    : out std_logic_vector(31 downto 0);
        imem_data    : in  std_logic_vector(31 downto 0);
        dmem_addr    : out std_logic_vector(31 downto 0);
        dmem_wdata   : out std_logic_vector(31 downto 0);
        dmem_rdata   : in  std_logic_vector(31 downto 0);
        dmem_we      : out std_logic;
        dmem_re      : out std_logic;
        dmem_width   : out std_logic_vector(1 downto 0);
        halted       : out std_logic;
        semi_trigger : out std_logic;
        semi_op      : out std_logic_vector(31 downto 0);
        semi_param   : out std_logic_vector(31 downto 0)
    );
end entity rv32i_core;

architecture rtl of rv32i_core is
    signal dmem_wstrb_i : std_logic_vector(3 downto 0);
    signal debug_pc_i   : std_logic_vector(31 downto 0);
    signal trap_i       : std_logic;
    signal halt_i       : std_logic;
begin
    u_core : entity work.simple_rv32gc_core
        port map (
            clk        => clk,
            reset_n    => reset_n,
            imem_addr  => imem_addr,
            imem_rdata => imem_data,
            dmem_addr  => dmem_addr,
            dmem_wdata => dmem_wdata,
            dmem_rdata => dmem_rdata,
            dmem_we    => dmem_we,
            dmem_re    => dmem_re,
            dmem_width => dmem_width,
            dmem_wstrb => dmem_wstrb_i,
            debug_pc   => debug_pc_i,
            semi_trigger => semi_trigger,
            semi_op    => semi_op,
            semi_param => semi_param,
            trap       => trap_i,
            halt       => halt_i
        );

    halted <= halt_i or trap_i;
end architecture rtl;
