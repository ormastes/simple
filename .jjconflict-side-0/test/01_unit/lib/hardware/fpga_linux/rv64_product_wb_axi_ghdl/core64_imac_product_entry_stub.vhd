library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use std.env.all;

-- Test-only stand-in for the compiler-emitted core ABI.  It submits a
-- byte read at +3, then an atomic 64-bit write at +8 and checks both replies.
entity core64_imac_product_entry is
  port (
    clk : in bit; reset_n : in bit; reset_vec : in signed(63 downto 0);
    msip, mtip, meip, stip, seip : in bit; time_value : in signed(63 downto 0);
    request_ready : in bit; response_valid : in bit; response_error : in bit;
    response_data : in signed(63 downto 0);
    bus_valid : out bit; bus_addr : out signed(63 downto 0);
    bus_size : out unsigned(31 downto 0); bus_write : out bit;
    bus_wdata : out signed(63 downto 0); bus_is_pte : out bit; bus_atomic : out bit;
    rvfi_valid : out bit; rvfi_order : out signed(63 downto 0); rvfi_insn : out signed(31 downto 0);
    rvfi_trap, rvfi_halt, rvfi_intr : out bit; rvfi_mode : out unsigned(1 downto 0);
    rvfi_ixl : out unsigned(1 downto 0); rvfi_rs1_addr, rvfi_rs2_addr : out unsigned(4 downto 0);
    rvfi_rs1_rdata, rvfi_rs2_rdata : out signed(63 downto 0); rvfi_rd_addr : out unsigned(4 downto 0);
    rvfi_rd_wdata, rvfi_pc_rdata, rvfi_pc_wdata, rvfi_mem_addr : out signed(63 downto 0);
    rvfi_mem_rmask, rvfi_mem_wmask : out unsigned(7 downto 0);
    rvfi_mem_rdata, rvfi_mem_wdata : out signed(63 downto 0)
  );
end entity;

architecture test of core64_imac_product_entry is
  type state_t is (wait_reset, read_request, read_response, write_request, write_response, done);
  signal state : state_t := wait_reset;
begin
  bus_valid <= '1' when state = read_request or state = write_request else '0';
  bus_addr <= signed'(x"0000000080000003") when state = read_request
              else signed'(x"0000000080000008");
  bus_size <= to_unsigned(1, 32) when state = read_request else to_unsigned(8, 32);
  bus_write <= '0' when state = read_request else '1';
  bus_wdata <= to_signed(16#11223344#, 64);
  bus_is_pte <= '0'; bus_atomic <= '1' when state = write_request else '0';
  rvfi_valid <= '0'; rvfi_order <= (others => '0'); rvfi_insn <= (others => '0');
  rvfi_trap <= '0'; rvfi_halt <= '0'; rvfi_intr <= '0'; rvfi_mode <= (others => '0'); rvfi_ixl <= (others => '0');
  rvfi_rs1_addr <= (others => '0'); rvfi_rs2_addr <= (others => '0'); rvfi_rs1_rdata <= (others => '0'); rvfi_rs2_rdata <= (others => '0');
  rvfi_rd_addr <= (others => '0'); rvfi_rd_wdata <= (others => '0'); rvfi_pc_rdata <= (others => '0'); rvfi_pc_wdata <= (others => '0');
  rvfi_mem_addr <= (others => '0'); rvfi_mem_rmask <= (others => '0'); rvfi_mem_wmask <= (others => '0'); rvfi_mem_rdata <= (others => '0'); rvfi_mem_wdata <= (others => '0');

  process(clk)
  begin
    if rising_edge(clk) then
      if reset_n = '0' then state <= wait_reset;
      else case state is
        when wait_reset => if request_ready = '1' then state <= read_request; end if;
        when read_request => if request_ready = '1' then state <= read_response; end if;
        when read_response => if response_valid = '1' then
          assert response_error = '0' and response_data(7 downto 0) = to_signed(-91, 8) report "byte-read response was not lane-normalized" severity failure;
          state <= write_request;
        end if;
        when write_request => if request_ready = '1' then state <= write_response; end if;
        when write_response => if response_valid = '1' then
          assert response_error = '1' report "AXI write error did not reach product core" severity failure;
          state <= done;
        end if;
        when done =>
          report "RV64_PRODUCT_WB_AXI_GHDL_PASS" severity note;
          finish;
      end case; end if;
    end if;
  end process;
end architecture;
