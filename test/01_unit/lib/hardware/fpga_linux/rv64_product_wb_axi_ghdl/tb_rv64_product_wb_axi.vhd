library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

entity tb_rv64_product_wb_axi is end entity;
architecture tb of tb_rv64_product_wb_axi is
  signal clk : std_logic := '0'; signal rst : std_logic := '1';
  signal adr, dat_o, dat_i : std_logic_vector(63 downto 0) := (others => '0');
  signal sel : std_logic_vector(7 downto 0); signal we, stb, cyc, lock, ack, err : std_logic := '0';
  signal awaddr, araddr : std_logic_vector(48 downto 0); signal awlen, arlen : std_logic_vector(7 downto 0);
  signal awsize, arsize : std_logic_vector(2 downto 0); signal awburst, arburst, bresp, rresp : std_logic_vector(1 downto 0);
  signal awlock, arlock, awvalid, wvalid, bready, arvalid, rready, awready, wready, bvalid, arready, rlast, rvalid : std_logic := '0';
  signal wdata, rdata : std_logic_vector(127 downto 0); signal wstrb : std_logic_vector(15 downto 0); signal wlast : std_logic;
  signal read_seen : boolean := false;
  signal write_phase : natural range 0 to 4 := 0;
  signal held_awaddr : std_logic_vector(48 downto 0) := (others => '0');
  signal held_wdata : std_logic_vector(127 downto 0) := (others => '0');
  signal held_wstrb : std_logic_vector(15 downto 0) := (others => '0');
begin
  clk <= not clk after 5 ns;
  process begin wait for 20 ns; rst <= '0'; wait for 1 us; assert false report "timeout" severity failure; end process;
  u_core: entity work.rv64imac_core_product_wb port map (
    clk=>clk, rst=>rst, msip_i=>'0', mtip_i=>'0', meip_i=>'0', stip_i=>'0', seip_i=>'0', time_value_i=>(others=>'0'),
    wb_adr_o=>adr, wb_dat_o=>dat_o, wb_dat_i=>dat_i, wb_we_o=>we, wb_sel_o=>sel, wb_stb_o=>stb, wb_cyc_o=>cyc, wb_lock_o=>lock, wb_ack_i=>ack, wb_err_i=>err);
  u_bridge: entity work.wb64_axi_hp_bridge port map (
    clk=>clk, rst=>rst, wb_adr_i=>adr, wb_dat_i=>dat_o, wb_dat_o=>dat_i, wb_we_i=>we, wb_sel_i=>sel, wb_stb_i=>stb, wb_cyc_i=>cyc, wb_lock_i=>lock, wb_ack_o=>ack, wb_err_o=>err,
    m_axi_awaddr=>awaddr, m_axi_awlen=>awlen, m_axi_awsize=>awsize, m_axi_awburst=>awburst, m_axi_awlock=>awlock, m_axi_awvalid=>awvalid, m_axi_awready=>awready,
    m_axi_wdata=>wdata, m_axi_wstrb=>wstrb, m_axi_wlast=>wlast, m_axi_wvalid=>wvalid, m_axi_wready=>wready, m_axi_bresp=>bresp, m_axi_bvalid=>bvalid, m_axi_bready=>bready,
    m_axi_araddr=>araddr, m_axi_arlen=>arlen, m_axi_arsize=>arsize, m_axi_arburst=>arburst, m_axi_arlock=>arlock, m_axi_arvalid=>arvalid, m_axi_arready=>arready,
    m_axi_rdata=>rdata, m_axi_rresp=>rresp, m_axi_rlast=>rlast, m_axi_rvalid=>rvalid, m_axi_rready=>rready);
  arready <= '1';
  process(clk)
  begin
    if rising_edge(clk) then
      bvalid <= '0'; rvalid <= '0'; bresp <= "00"; rresp <= "00"; rlast <= '1';
      if arvalid = '1' then
        assert adr = x"0000000080000003" and sel = x"08" report "byte lane was not preserved through wrapper" severity failure;
        assert araddr = std_logic_vector(to_unsigned(16#40000000#, 49)) report "AXI read address translation/alignment is wrong" severity failure;
        read_seen <= true;
      end if;
      if read_seen and rready = '1' then rdata <= x"000000000000000000000000A5000000"; rvalid <= '1'; read_seen <= false; end if;
      case write_phase is
        when 0 =>
          if awvalid = '1' and wvalid = '1' then
            assert awaddr = std_logic_vector(to_unsigned(16#40000008#, 49)) report "AXI write address translation is wrong" severity failure;
            assert wstrb = x"FF00" and wdata(95 downto 64) = x"11223344" report "upper 128-bit AXI write lane is wrong" severity failure;
            assert awlock = '0' and arlock = '0' report "Wishbone atomic lock must not become AXI exclusive" severity failure;
            held_awaddr <= awaddr; held_wdata <= wdata; held_wstrb <= wstrb;
            write_phase <= 1;
          end if;
        when 1 =>
          assert awvalid = '1' and wvalid = '1' report "AXI valid dropped under backpressure" severity failure;
          assert awaddr = held_awaddr and wdata = held_wdata and wstrb = held_wstrb report "AXI payload changed under backpressure" severity failure;
          wready <= '1';
          write_phase <= 2;
        when 2 =>
          assert awvalid = '1' and awaddr = held_awaddr report "AW channel was not held after W completed" severity failure;
          wready <= '0'; awready <= '1';
          write_phase <= 3;
        when 3 =>
          awready <= '0';
          if bready = '1' then bresp <= "10"; bvalid <= '1'; write_phase <= 4; end if;
        when others => null;
      end case;
    end if;
  end process;
end architecture;
