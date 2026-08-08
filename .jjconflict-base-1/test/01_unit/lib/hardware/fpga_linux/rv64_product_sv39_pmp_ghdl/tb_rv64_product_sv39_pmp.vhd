library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use ieee.std_logic_textio.all;
use std.textio.all;
use std.env.all;

entity tb_rv64_product_sv39_pmp is
  generic (PROGRAM_HEX : string := "rv64_product_sv39_pmp.hex");
end entity;

architecture tb of tb_rv64_product_sv39_pmp is
  signal clk : std_logic := '0';
  signal rst : std_logic := '1';
  signal adr, dat_o, dat_i : std_logic_vector(63 downto 0) := (others => '0');
  signal sel : std_logic_vector(7 downto 0);
  signal we, stb, cyc, lock, ack, err : std_logic := '0';
  signal root_seen, l1_seen, l0_seen : boolean := false;

  impure function image_byte(addr : unsigned(63 downto 0)) return std_logic_vector is
    file image : text open read_mode is PROGRAM_HEX;
    variable row : line;
    variable image_addr : std_logic_vector(63 downto 0);
    variable image_data : std_logic_vector(7 downto 0);
    variable good : boolean;
  begin
    while not endfile(image) loop
      readline(image, row);
      hread(row, image_addr, good);
      if good then
        hread(row, image_data, good);
        if good and unsigned(image_addr) = addr then return image_data; end if;
      end if;
    end loop;
    return x"00";
  end function;

  impure function program_qword(addr : std_logic_vector(63 downto 0)) return std_logic_vector is
    variable data : std_logic_vector(63 downto 0) := (others => '0');
    variable base : unsigned(63 downto 0) := unsigned(addr) and x"FFFFFFFFFFFFFFF8";
  begin
    for byte in 0 to 7 loop
      data(byte * 8 + 7 downto byte * 8) := image_byte(base + to_unsigned(byte, 64));
    end loop;
    return data;
  end function;

  impure function ram_qword(addr : std_logic_vector(63 downto 0)) return std_logic_vector is
  begin
    -- Sv39 root[1]/l1[0]/l0[0]: VA 0x40000000 -> denied PA 0x40000000.
    if addr = x"0000000080001008" then return x"0000000020001001"; end if;
    if addr = x"0000000080004000" then return x"0000000020001401"; end if;
    if addr = x"0000000080005000" then return x"0000000010000043"; end if;
    -- Sv39 root[2]/l1[0]/l0[0]: S-mode program page maps to itself.
    if addr = x"0000000080001010" then return x"0000000020000801"; end if;
    if addr = x"0000000080002000" then return x"0000000020000C01"; end if;
    if addr = x"0000000080003000" then return x"000000002000004B"; end if;
    return program_qword(addr);
  end function;
begin
  clk <= not clk after 5 ns;
  process begin
    wait for 30 ns; rst <= '0';
    wait for 80 us;
    assert false report "RV64 Sv39/PMP product test timed out" severity failure;
  end process;

  dut : entity work.rv64imac_core_product_wb
    port map (
      clk => clk, rst => rst, msip_i => '0', mtip_i => '0', meip_i => '0',
      stip_i => '0', seip_i => '0', time_value_i => (others => '0'),
      wb_adr_o => adr, wb_dat_o => dat_o, wb_dat_i => dat_i, wb_we_o => we,
      wb_sel_o => sel, wb_stb_o => stb, wb_cyc_o => cyc, wb_lock_o => lock,
      wb_ack_i => ack, wb_err_i => err);

  process(clk)
  begin
    if rising_edge(clk) then
      ack <= '0';
      err <= '0';
      if cyc = '1' and stb = '1' then
        assert adr /= x"0000000040000000"
          report "PMP-denied final translated target reached Wishbone" severity failure;
        assert not (we = '1' and adr = x"0000000040000000")
          report "PMP-denied target issued a Wishbone write" severity failure;
        dat_i <= ram_qword(adr);
        ack <= '1';
        if we = '0' and adr = x"0000000080001008" and sel = x"FF" then root_seen <= true; end if;
        if we = '0' and adr = x"0000000080004000" and sel = x"FF" then l1_seen <= true; end if;
        if we = '0' and adr = x"0000000080005000" and sel = x"FF" then l0_seen <= true; end if;
        if we = '1' and adr = x"0000000010000000" then
          assert sel = x"FF" and dat_o = x"0000000000000005"
            report "expected S-mode load access fault mcause 5" severity failure;
          assert root_seen and l1_seen and l0_seen
            report "expected Sv39 walker PTE reads were not all observed" severity failure;
          report "RV64_PRODUCT_SV39_PMP_GHDL_PASS" severity note;
          finish;
        end if;
      end if;
    end if;
  end process;
end architecture;
