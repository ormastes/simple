library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use std.textio.all;
use ieee.std_logic_textio.all;

entity tb_rv32_product_sv32_pmp is end entity;

architecture tb of tb_rv32_product_sv32_pmp is
  constant MEM_WORDS : natural := 4096;
  type mem_t is array (0 to MEM_WORDS - 1) of std_logic_vector(31 downto 0);
  impure function init_program return mem_t is
    file source : text open read_mode is "rv32_product_sv32_pmp.mem";
    variable result : mem_t := (others => (others => '0'));
    variable row : line; variable word : std_logic_vector(31 downto 0);
    variable good : boolean; variable index : natural := 0;
  begin
    while not endfile(source) loop
      readline(source, row);
      if row'length > 0 and row.all(row.all'low) /= '@' then
        hread(row, word, good);
        if good and index < MEM_WORDS then result(index) := word; index := index + 1; end if;
      end if;
    end loop;
    return result;
  end function;
  signal program : mem_t := init_program;
  signal clk : std_logic := '0'; signal rst : std_logic := '1';
  signal adr : std_logic_vector(63 downto 0); signal dat_o, dat_i : std_logic_vector(63 downto 0) := (others => '0');
  signal sel : std_logic_vector(7 downto 0); signal we, stb, cyc, lock, ack, err : std_logic := '0';
  signal code_root, code_leaf, target_root, target_leaf, denied_target : boolean := false;
begin
  clk <= not clk after 5 ns;
  ack <= cyc and stb;
  err <= '0';
  process(all)
    variable a : natural; variable d : std_logic_vector(31 downto 0);
  begin
    a := to_integer(unsigned(adr(31 downto 0)));
    d := (others => '0');
    if a < MEM_WORDS * 4 then d := program(a / 4);
    elsif a = 16#4800# then d := x"00001401"; -- VPN1=512 -> leaf at 0x5000
    elsif a = 16#4400# then d := x"00001801"; -- VPN1=256 -> leaf at 0x6000
    elsif a = 16#5000# then d := x"0000004B"; -- physical code page, R/X/A/V
    elsif a = 16#6000# then d := x"000020C7"; -- physical 0x8000, R/W/A/D/V
    end if;
    if adr(2) = '0' then dat_i <= x"00000000" & d;
    else dat_i <= d & x"00000000";
    end if;
  end process;
  u_dut: entity work.rv32imac_core_product_wb
    generic map (RESET_ADDR => x"0000000000000000")
    port map (clk=>clk, rst=>rst, msip_i=>'0', mtip_i=>'0', meip_i=>'0', stip_i=>'0', seip_i=>'0', time_value_i=>(others=>'0'),
      wb_adr_o=>adr, wb_dat_o=>dat_o, wb_dat_i=>dat_i, wb_we_o=>we, wb_sel_o=>sel, wb_stb_o=>stb, wb_cyc_o=>cyc, wb_lock_o=>lock, wb_ack_i=>ack, wb_err_i=>err);
  process
  begin
    wait for 20 ns; rst <= '0'; wait for 20 us;
    assert false report "timeout waiting for Sv32/PMP trap" severity failure;
  end process;
  process(clk)
    variable a : natural;
  begin
    if rising_edge(clk) and cyc = '1' and stb = '1' then
      a := to_integer(unsigned(adr(31 downto 0)));
      if we = '0' and sel = x"0F" and a = 16#4800# then code_root <= true; end if;
      if we = '0' and sel = x"0F" and a = 16#5000# then code_leaf <= true; end if;
      if we = '0' and sel = x"0F" and a = 16#4400# then target_root <= true; end if;
      if we = '0' and sel = x"0F" and a = 16#6000# then target_leaf <= true; end if;
      if a = 16#8000# then denied_target <= true; end if;
      if a = 16#9000# and we = '1' then
        assert code_root and code_leaf and target_root and target_leaf
          report "Sv32 code and target walker PTE reads were not all observed" severity failure;
        assert not denied_target report "PMP-denied translated target reached Wishbone" severity failure;
        assert dat_o(31 downto 0) = x"00000005" report "expected S-mode load access fault trap" severity failure;
        report "RV32_PRODUCT_SV32_PMP_GHDL_PASS" severity note;
        std.env.finish;
      end if;
    end if;
  end process;
end architecture;
