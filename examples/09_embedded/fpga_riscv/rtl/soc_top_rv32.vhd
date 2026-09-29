library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
library unisim;
use unisim.vcomponents.all;

entity soc_top_rv32 is
  generic (
    RESET_RELEASE_COUNT : natural := 255
  );
  port (
    uart_tx : out std_logic
  );
end entity soc_top_rv32;

architecture rtl of soc_top_rv32 is
  signal cfgclk  : std_logic;
  signal cfgmclk : std_logic;
  signal di      : std_logic_vector(3 downto 0);
  signal eos     : std_logic;
  signal preq    : std_logic;
  signal rst_q   : std_logic := '1';
  signal rst_cnt : unsigned(31 downto 0) := (others => '0');
  signal uart_tx_core : std_logic;
  signal debug_uart_valid : std_logic;
  signal debug_uart_byte : std_logic_vector(7 downto 0);
  signal debug_pc : std_logic_vector(15 downto 0);
  signal debug_ins : std_logic_vector(31 downto 0);
  signal debug_a0 : std_logic_vector(7 downto 0);
  signal debug_ra : std_logic_vector(15 downto 0);
  signal debug_sp : std_logic_vector(15 downto 0);
  signal debug_phase : std_logic_vector(3 downto 0);
  signal marker_idx : natural range 0 to 8 := 0;
  signal marker_seen : std_logic := '0';
  signal uart_ila_probe : std_logic_vector(101 downto 0);
  function marker_byte(idx : natural) return std_logic_vector is
  begin
    case idx is
      when 0 => return x"46";
      when 1 => return x"50";
      when 2 => return x"47";
      when 3 => return x"41";
      when 4 => return x"2D";
      when 5 => return x"52";
      when 6 => return x"56";
      when 7 => return x"33";
      when others => return x"32";
    end case;
  end function;
  attribute dont_touch : string;
  attribute mark_debug : string;
  attribute dont_touch of uart_tx_core : signal is "true";
  attribute mark_debug of uart_tx_core : signal is "true";
  attribute dont_touch of uart_ila_probe : signal is "true";
  attribute mark_debug of uart_ila_probe : signal is "true";
begin
  uart_tx <= uart_tx_core;
  uart_ila_probe(7 downto 0) <= debug_uart_byte;
  uart_ila_probe(8) <= debug_uart_valid;
  uart_ila_probe(9) <= marker_seen;
  uart_ila_probe(25 downto 10) <= debug_pc;
  uart_ila_probe(57 downto 26) <= debug_ins;
  uart_ila_probe(65 downto 58) <= debug_a0;
  uart_ila_probe(81 downto 66) <= debug_ra;
  uart_ila_probe(97 downto 82) <= debug_sp;
  uart_ila_probe(101 downto 98) <= debug_phase;

  u_startup : STARTUPE3
    generic map (PROG_USR => "FALSE", SIM_CCLK_FREQ => 0.0)
    port map (
      CFGCLK => cfgclk, CFGMCLK => cfgmclk, DI => di, EOS => eos, PREQ => preq,
      DO => "0000", DTS => "1111", FCSBO => '1', FCSBTS => '1', GSR => '0', GTS => '0',
      KEYCLEARB => '1', PACK => '0', USRCCLKO => '0', USRCCLKTS => '1',
      USRDONEO => '1', USRDONETS => '1'
    );

  process(cfgmclk)
  begin
    if rising_edge(cfgmclk) then
      if rst_cnt < to_unsigned(RESET_RELEASE_COUNT, rst_cnt'length) then
        rst_cnt <= rst_cnt + 1;
        rst_q <= '1';
      else
        rst_q <= '0';
      end if;
    end if;
  end process;

  process(cfgmclk)
  begin
    if rising_edge(cfgmclk) then
      if rst_q = '1' then
        marker_idx <= 0;
        marker_seen <= '0';
      elsif debug_uart_valid = '1' then
        if debug_uart_byte = marker_byte(marker_idx) then
          if marker_idx = 8 then
            marker_seen <= '1';
            marker_idx <= 0;
          else
            marker_idx <= marker_idx + 1;
          end if;
        elsif debug_uart_byte = marker_byte(0) then
          marker_idx <= 1;
        else
          marker_idx <= 0;
        end if;
      end if;
    end if;
  end process;

  u_core : entity work.rv32_exec_core
    port map (
      clk => cfgmclk, rst => rst_q, uart_tx => uart_tx_core,
      debug_uart_valid => debug_uart_valid,
      debug_uart_byte => debug_uart_byte,
      debug_pc => debug_pc,
      debug_ins => debug_ins,
      debug_a0 => debug_a0,
      debug_ra => debug_ra,
      debug_sp => debug_sp,
      debug_phase => debug_phase
    );
end architecture rtl;
