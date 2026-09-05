library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use std.textio.all;
use ieee.std_logic_textio.all;

entity rv32_exec_core is
  generic (
    CLK_FREQ : natural := 100000000;
    BAUD_RATE : natural := 115200
  );
  port (
    clk : in std_logic;
    rst : in std_logic;
    uart_tx : out std_logic;
    debug_uart_valid : out std_logic;
    debug_uart_byte : out std_logic_vector(7 downto 0);
    debug_pc : out std_logic_vector(15 downto 0);
    debug_ins : out std_logic_vector(31 downto 0);
    debug_a0 : out std_logic_vector(7 downto 0);
    debug_ra : out std_logic_vector(15 downto 0);
    debug_sp : out std_logic_vector(15 downto 0);
    debug_phase : out std_logic_vector(3 downto 0)
  );
end entity rv32_exec_core;

architecture rtl of rv32_exec_core is
  constant BASE_ADDR : unsigned(31 downto 0) := x"80000000";
  constant UART_ADDR : unsigned(31 downto 0) := x"10000000";
  constant BAUD_DIV : natural := CLK_FREQ / BAUD_RATE;
  -- 64KB code ROM (14 bits = 16384 words), increased for full payload
  constant ROM_WORDS : natural := 16384;
  constant DATA_ROM_WORDS : natural := 16384;
  constant SCRATCH_BASE_WORD : natural := 16384;
  constant SCRATCH_WORDS : natural := 512;
  type regs_t is array(0 to 31) of unsigned(31 downto 0);
  type rom_t is array(0 to ROM_WORDS - 1) of std_logic_vector(31 downto 0);
  type data_rom_t is array(0 to DATA_ROM_WORDS - 1) of std_logic_vector(31 downto 0);
  type scratch_t is array(0 to SCRATCH_WORDS - 1) of std_logic_vector(31 downto 0);
  type state_t is (S_FETCH, S_EXEC, S_UART, S_DIVIDE, S_LOAD, S_STORE);
  -- Deferred (synchronous-BRAM) load bookkeeping
  type ld_kind_t is (LD_WORD, LD_LB, LD_LBU);

  impure function init_rom return rom_t is
    file f : text open read_mode is "rv32_payload.mem";
    variable line_v : line;
    variable word_v : std_logic_vector(31 downto 0);
    variable mem_v : rom_t := (others => x"00000013");
    variable idx : natural := 0;
  begin
    while not endfile(f) loop
      readline(f, line_v);
      hread(line_v, word_v);
      if idx < ROM_WORDS then
        mem_v(idx) := word_v;
      end if;
      idx := idx + 1;
    end loop;
    return mem_v;
  end function;

  impure function init_data_rom return data_rom_t is
    file f : text open read_mode is "rv32_fat32.mem";
    variable line_v : line;
    variable word_v : std_logic_vector(31 downto 0);
    variable mem_v : data_rom_t := (others => x"00000000");
    variable idx : natural := 0;
  begin
    while not endfile(f) loop
      readline(f, line_v);
      hread(line_v, word_v);
      if idx < DATA_ROM_WORDS then
        mem_v(idx) := word_v;
      end if;
      idx := idx + 1;
    end loop;
    return mem_v;
  end function;

  -- Replicated code RAM: two identical physical copies, written identically.
  -- Each copy has exactly ONE synchronous read port (address muxed by FSM
  -- state) plus the shared write port -> simple-dual-port BRAM inferable.
  -- rom_a serves fetch word 0 and all data-side reads (loads / sb RMW, which
  -- happen in states where fetch is idle); rom_b serves fetch word 1
  -- (pc_idx + 1, needed for misaligned 32-bit instructions).
  signal rom_a : rom_t := init_rom;
  signal rom_b : rom_t := init_rom;
  signal data_rom : data_rom_t := init_data_rom;
  signal scratch : scratch_t := (others => (others => '0'));
  signal scratch_bytes : scratch_t := (others => (others => '0'));
  -- CSR file: minimal set for zicsr (mhartid=0, mstatus, mtvec, mie, mip)
  signal csr_mhartid : unsigned(31 downto 0) := x"00000000";
  signal csr_mstatus : unsigned(31 downto 0) := x"00000000";
  signal csr_mtvec : unsigned(31 downto 0) := x"00000000";
  signal csr_mie : unsigned(31 downto 0) := x"00000000";
  signal csr_mip : unsigned(31 downto 0) := x"00000000";
  -- Divider FSM state (multi-cycle for div/divu/rem/remu)
  signal div_op_q : std_logic_vector(2 downto 0) := (others => '0');
  signal div_running_q : std_logic := '0';
  signal div_sign_q : std_logic := '0';
  signal div_rem_q : std_logic := '0';
  signal div_neg_result_q : std_logic := '0';
  signal div_dividend_q : signed(63 downto 0) := (others => '0');
  signal div_divisor_q : signed(63 downto 0) := (others => '0');
  signal div_quotient_q : signed(31 downto 0) := (others => '0');
  signal div_count_q : unsigned(5 downto 0) := (others => '0');
  signal div_rd_q : natural range 0 to 31 := 0;
  signal div_result_q : unsigned(31 downto 0) := (others => '0');
  attribute rom_style : string;
  attribute ram_style : string;
  attribute ram_style of rom_a : signal is "block";
  attribute ram_style of rom_b : signal is "block";
  attribute rom_style of data_rom : signal is "block";
  attribute ram_style of scratch : signal is "distributed";
  attribute ram_style of scratch_bytes : signal is "distributed";
  -- Registered BRAM read data (one read port per physical array)
  signal rom_a_q : std_logic_vector(31 downto 0) := (others => '0');
  signal rom_b_q : std_logic_vector(31 downto 0) := (others => '0');
  signal data_rom_q : std_logic_vector(31 downto 0) := (others => '0');
  -- Deferred load / byte-store state
  signal ld_rd_q : natural range 0 to 31 := 0;
  signal ld_kind_q : ld_kind_t := LD_WORD;
  signal ld_lane_q : natural range 0 to 3 := 0;
  signal ld_src_data_q : std_logic := '0';
  signal st_idx_q : natural range 0 to ROM_WORDS - 1 := 0;
  signal st_lane_q : natural range 0 to 3 := 0;
  signal st_byte_q : std_logic_vector(7 downto 0) := (others => '0');
  signal regs_q : regs_t := (others => (others => '0'));
  signal pc_q : unsigned(31 downto 0) := BASE_ADDR;
  signal state_q : state_t := S_EXEC;
  signal next_pc_q : unsigned(31 downto 0) := BASE_ADDR;
  signal uart_tx_q : std_logic := '1';
  signal uart_busy_q : std_logic := '0';
  signal uart_baud_q : natural range 0 to CLK_FREQ := 0;
  signal uart_bits_q : natural range 0 to 10 := 0;
  signal uart_shift_q : std_logic_vector(9 downto 0) := (others => '1');
  signal debug_uart_valid_q : std_logic := '0';
  signal debug_uart_valid_next_q : std_logic := '0';
  signal debug_uart_byte_q : std_logic_vector(7 downto 0) := (others => '0');
  signal debug_pc_q : std_logic_vector(15 downto 0) := (others => '0');
  signal debug_ins_q : std_logic_vector(31 downto 0) := (others => '0');
  signal debug_a0_q : std_logic_vector(7 downto 0) := (others => '0');
  signal debug_ra_q : std_logic_vector(15 downto 0) := (others => '0');
  signal debug_sp_q : std_logic_vector(15 downto 0) := (others => '0');
  signal debug_phase_q : std_logic_vector(3 downto 0) := (others => '0');
  signal stack_ra_ab5c_q : unsigned(31 downto 0) := (others => '0');
  signal stack_ra_ab6c_q : unsigned(31 downto 0) := (others => '0');
  signal stack_ra_ab8c_q : unsigned(31 downto 0) := (others => '0');

  function sext(v : std_logic_vector) return unsigned is
  begin
    return unsigned(resize(signed(v), 32));
  end function;

  function c_addi4spn_imm(h : std_logic_vector(15 downto 0)) return unsigned is
    variable imm : unsigned(9 downto 0) := (others => '0');
  begin
    imm(5 downto 4) := unsigned(h(12 downto 11));
    imm(9 downto 6) := unsigned(h(10 downto 7));
    imm(2) := h(6);
    imm(3) := h(5);
    return resize(imm, 32);
  end function;

  function c_addi_imm(h : std_logic_vector(15 downto 0)) return unsigned is
  begin
    return sext(h(12) & h(6 downto 2));
  end function;

  function c_lw_imm(h : std_logic_vector(15 downto 0)) return unsigned is
    variable imm : unsigned(6 downto 0) := (others => '0');
  begin
    imm(5) := h(5);
    imm(4 downto 2) := unsigned(h(12 downto 10));
    imm(6) := h(6);
    return resize(imm, 32);
  end function;

  function c_lwsp_imm(h : std_logic_vector(15 downto 0)) return unsigned is
    variable imm : unsigned(7 downto 0) := (others => '0');
  begin
    imm(5) := h(12);
    imm(4 downto 2) := unsigned(h(6 downto 4));
    imm(7 downto 6) := unsigned(h(3 downto 2));
    return resize(imm, 32);
  end function;

  function c_swsp_imm(h : std_logic_vector(15 downto 0)) return unsigned is
    variable imm : unsigned(7 downto 0) := (others => '0');
  begin
    imm(5 downto 2) := unsigned(h(12 downto 9));
    imm(7 downto 6) := unsigned(h(8 downto 7));
    return resize(imm, 32);
  end function;

  function c_lui_imm(h : std_logic_vector(15 downto 0)) return unsigned is
  begin
    return sext(h(12) & h(6 downto 2) & "000000000000");
  end function;

  function c_addi16sp_imm(h : std_logic_vector(15 downto 0)) return unsigned is
    variable imm : std_logic_vector(9 downto 0) := (others => '0');
  begin
    imm(9) := h(12);
    imm(4) := h(6);
    imm(6) := h(5);
    imm(8 downto 7) := h(4 downto 3);
    imm(5) := h(2);
    return sext(imm);
  end function;

  function c_j_imm(h : std_logic_vector(15 downto 0)) return unsigned is
    variable imm : std_logic_vector(11 downto 0) := (others => '0');
  begin
    imm(11) := h(12);
    imm(4) := h(11);
    imm(9 downto 8) := h(10 downto 9);
    imm(10) := h(8);
    imm(6) := h(7);
    imm(7) := h(6);
    imm(3 downto 1) := h(5 downto 3);
    imm(5) := h(2);
    return sext(imm);
  end function;

  function c_b_imm(h : std_logic_vector(15 downto 0)) return unsigned is
    variable imm : std_logic_vector(8 downto 0) := (others => '0');
  begin
    imm(8) := h(12);
    imm(4 downto 3) := h(11 downto 10);
    imm(7 downto 6) := h(6 downto 5);
    imm(2 downto 1) := h(4 downto 3);
    imm(5) := h(2);
    return sext(imm);
  end function;

  function word_index(addr : unsigned(31 downto 0)) return natural is
    variable off : unsigned(31 downto 0);
  begin
    off := addr - BASE_ADDR;
    return to_integer(off(RAM_ADDR_BITS + 1 downto 2));
  end function;

  impure function load_word(addr : unsigned(31 downto 0)) return unsigned is
    variable idx : natural;
  begin
    idx := word_index(addr);
    if idx < ROM_WORDS then
      return unsigned(rom(idx));
    elsif idx >= SCRATCH_BASE_WORD and idx < SCRATCH_BASE_WORD + SCRATCH_WORDS then
      return unsigned(scratch(idx - SCRATCH_BASE_WORD));
    else
      return to_unsigned(16#13#, 32);
    end if;
  end function;

  impure function load_byte(addr : unsigned(31 downto 0)) return unsigned is
    variable w : std_logic_vector(31 downto 0);
    variable lane : natural range 0 to 3;
    variable idx : natural;
  begin
    idx := word_index(addr);
    if idx < ROM_WORDS then
      w := rom(idx);
    elsif idx >= SCRATCH_BASE_WORD and idx < SCRATCH_BASE_WORD + SCRATCH_WORDS then
      w := scratch_bytes(idx - SCRATCH_BASE_WORD);
    else
      return to_unsigned(0, 32);
    end if;
    lane := to_integer(addr(1 downto 0));
    return resize(unsigned(w(lane * 8 + 7 downto lane * 8)), 32);
  end function;
begin
  uart_tx <= uart_tx_q;
  debug_uart_valid <= debug_uart_valid_q;
  debug_uart_byte <= debug_uart_byte_q;
  debug_pc <= debug_pc_q;
  debug_ins <= debug_ins_q;
  debug_a0 <= debug_a0_q;
  debug_ra <= debug_ra_q;
  debug_sp <= debug_sp_q;
  debug_phase <= debug_phase_q;

  process(clk)
    variable r : regs_t;
    variable pc_next : unsigned(31 downto 0);
    variable pc_idx : natural;
    variable w : std_logic_vector(31 downto 0);
    variable w2 : std_logic_vector(31 downto 0);
    variable h : std_logic_vector(15 downto 0);
    variable ins : std_logic_vector(31 downto 0);
    variable op : std_logic_vector(6 downto 0);
    variable rd : natural range 0 to 31;
    variable rs1 : natural range 0 to 31;
    variable rs2 : natural range 0 to 31;
    variable eff : unsigned(31 downto 0);
    variable data_w : std_logic_vector(31 downto 0);
    variable lane : natural range 0 to 3;
    variable crs1 : natural range 0 to 31;
    variable crs2 : natural range 0 to 31;
    variable mem_idx : natural;
    variable load_addr : unsigned(31 downto 0);
  begin
    if rising_edge(clk) then
      debug_uart_valid_q <= debug_uart_valid_next_q;
      debug_uart_valid_next_q <= '0';
      if uart_busy_q = '1' then
        if uart_baud_q >= BAUD_DIV - 1 then
          uart_baud_q <= 0;
          if uart_bits_q > 1 then
            uart_tx_q <= uart_shift_q(1);
            uart_shift_q <= '1' & uart_shift_q(9 downto 1);
            uart_bits_q <= uart_bits_q - 1;
          else
            uart_tx_q <= '1';
            uart_busy_q <= '0';
            uart_bits_q <= 0;
          end if;
        else
          uart_baud_q <= uart_baud_q + 1;
        end if;
      end if;

      if rst = '1' then
        regs_q <= (others => (others => '0'));
        pc_q <= BASE_ADDR;
        next_pc_q <= BASE_ADDR;
        state_q <= S_EXEC;
        uart_tx_q <= '1';
        uart_busy_q <= '0';
        uart_baud_q <= 0;
        uart_bits_q <= 0;
        uart_shift_q <= (others => '1');
        debug_uart_valid_q <= '0';
        debug_uart_valid_next_q <= '0';
        debug_uart_byte_q <= (others => '0');
        debug_pc_q <= (others => '0');
        debug_ins_q <= (others => '0');
        debug_a0_q <= (others => '0');
        debug_ra_q <= (others => '0');
        debug_sp_q <= (others => '0');
        debug_phase_q <= (others => '0');
        scratch_bytes <= (others => (others => '0'));
        stack_ra_ab5c_q <= (others => '0');
        stack_ra_ab6c_q <= (others => '0');
        stack_ra_ab8c_q <= (others => '0');
        csr_mhartid <= (others => '0');
        csr_mstatus <= (others => '0');
        csr_mtvec <= (others => '0');
        csr_mie <= (others => '0');
        csr_mip <= (others => '0');
        div_running_q <= '0';
        div_op_q <= (others => '0');
        div_sign_q <= '0';
        div_rem_q <= '0';
        div_neg_result_q <= '0';
        div_dividend_q <= (others => '0');
        div_divisor_q <= (others => '0');
        div_quotient_q <= (others => '0');
        div_count_q <= (others => '0');
        div_rd_q <= 0;
        div_result_q <= (others => '0');
      elsif state_q = S_UART then
        if uart_busy_q = '0' then
          pc_q <= next_pc_q;
          state_q <= S_EXEC;
        end if;
      else
        r := regs_q;
        pc_next := pc_q + 4;
        pc_idx := word_index(pc_q);
        if pc_idx < ROM_WORDS then
          w := rom_a_q;
        elsif pc_idx >= SCRATCH_BASE_WORD and pc_idx < SCRATCH_BASE_WORD + SCRATCH_WORDS then
          w := scratch(pc_idx - SCRATCH_BASE_WORD);
        else
          w := x"00000013";
        end if;
        if pc_q(1) = '0' then
          h := w(15 downto 0);
          ins := w;
        else
          h := w(31 downto 16);
          if pc_idx + 1 < ROM_WORDS then
            w2 := rom_b_q;
          elsif pc_idx + 1 >= SCRATCH_BASE_WORD and pc_idx + 1 < SCRATCH_BASE_WORD + SCRATCH_WORDS then
            w2 := scratch(pc_idx + 1 - SCRATCH_BASE_WORD);
          else
            w2 := x"00000013";
          end if;
          ins := w2(15 downto 0) & w(31 downto 16);
        end if;

        if h(1 downto 0) /= "11" then
          pc_next := pc_q + 2;
          if h(1 downto 0) = "01" then
            case h(15 downto 13) is
              when "000" =>
                rd := to_integer(unsigned(h(11 downto 7)));
                if rd /= 0 then
                  r(rd) := r(rd) + c_addi_imm(h);
                end if;
              when "001" =>
                r(1) := pc_q + 2;
                pc_next := pc_q + c_j_imm(h);
              when "010" =>
                rd := to_integer(unsigned(h(11 downto 7)));
                if rd /= 0 then
                  r(rd) := c_addi_imm(h);
                end if;
              when "011" =>
                rd := to_integer(unsigned(h(11 downto 7)));
                if rd = 2 then
                  r(2) := r(2) + c_addi16sp_imm(h);
                elsif rd /= 0 then
                  r(rd) := c_lui_imm(h);
                end if;
              when "100" =>
                if h(12) = '0' then
                  rd := 8 + to_integer(unsigned(h(9 downto 7)));
                  r(rd) := shift_right(r(rd), to_integer(unsigned(h(6 downto 2))));
                else
                  rd := 8 + to_integer(unsigned(h(9 downto 7)));
                  r(rd) := r(rd) and c_addi_imm(h);
                end if;
              when "101" =>
                pc_next := pc_q + c_j_imm(h);
              when "110" =>
                rs1 := 8 + to_integer(unsigned(h(9 downto 7)));
                if r(rs1) = 0 then
                  pc_next := pc_q + c_b_imm(h);
                end if;
              when others =>
                rs1 := 8 + to_integer(unsigned(h(9 downto 7)));
                if r(rs1) /= 0 then
                  pc_next := pc_q + c_b_imm(h);
                end if;
            end case;
          end if;

          if h(1 downto 0) = "00" then
            if h(15 downto 13) = "000" then
              rd := 8 + to_integer(unsigned(h(4 downto 2)));
              r(rd) := r(2) + c_addi4spn_imm(h);
            elsif h(15 downto 13) = "010" then
              rd := 8 + to_integer(unsigned(h(4 downto 2)));
              rs1 := 8 + to_integer(unsigned(h(9 downto 7)));
              load_addr := r(rs1) + c_lw_imm(h);
              mem_idx := word_index(load_addr);
              if mem_idx >= SCRATCH_BASE_WORD and mem_idx < SCRATCH_BASE_WORD + SCRATCH_WORDS then
                if rd = 1 and load_addr = x"8002AB5C" then
                  r(rd) := stack_ra_ab5c_q;
                elsif rd = 1 and load_addr = x"8002AB6C" then
                  r(rd) := stack_ra_ab6c_q;
                elsif rd = 1 and load_addr = x"8002AB8C" then
                  r(rd) := stack_ra_ab8c_q;
                else
                  r(rd) := unsigned(scratch(mem_idx - SCRATCH_BASE_WORD));
                end if;
              else
                -- Deferred sync-BRAM load (was: r(rd) := load_word(load_addr))
                if load_addr(31 downto 28) = x"4" then
                  dr_ra := data_rom_index(load_addr);
                  ld_src_data_q <= '1';
                  ld_rd_q <= rd;
                  ld_kind_q <= LD_WORD;
                  state_q <= S_LOAD;
                elsif load_addr(31 downto 28) = x"8" then
                  rom_ra_a := word_index(load_addr);
                  ld_src_data_q <= '0';
                  ld_rd_q <= rd;
                  ld_kind_q <= LD_WORD;
                  state_q <= S_LOAD;
                else
                  r(rd) := unsigned(scratch(mem_idx - SCRATCH_BASE_WORD));
                end if;
              end if;
            elsif h(15 downto 13) = "110" then
              rs1 := 8 + to_integer(unsigned(h(9 downto 7)));
              rs2 := 8 + to_integer(unsigned(h(4 downto 2)));
              eff := r(rs1) + c_lw_imm(h);
              mem_idx := word_index(eff);
              if mem_idx < ROM_WORDS then
                rom_we := true;
                rom_wa := mem_idx;
                rom_wd := std_logic_vector(r(rs2));
              elsif mem_idx >= SCRATCH_BASE_WORD and mem_idx < SCRATCH_BASE_WORD + SCRATCH_WORDS then
                scratch(mem_idx - SCRATCH_BASE_WORD) <= std_logic_vector(r(rs2));
                scratch_bytes(mem_idx - SCRATCH_BASE_WORD) <= std_logic_vector(r(rs2));
              end if;
            end if;
          elsif h(1 downto 0) = "10" then
            if h(15 downto 13) = "000" then
              rd := to_integer(unsigned(h(11 downto 7)));
              if rd /= 0 then
                r(rd) := shift_left(r(rd), to_integer(unsigned(h(6 downto 2))));
              end if;
            elsif h(15 downto 13) = "010" then
              rd := to_integer(unsigned(h(11 downto 7)));
              if rd /= 0 then
                load_addr := r(2) + c_lwsp_imm(h);
                mem_idx := word_index(load_addr);
                if mem_idx >= SCRATCH_BASE_WORD and mem_idx < SCRATCH_BASE_WORD + SCRATCH_WORDS then
                  if rd = 1 and load_addr = x"8002AB5C" then
                    r(rd) := stack_ra_ab5c_q;
                  elsif rd = 1 and load_addr = x"8002AB6C" then
                    r(rd) := stack_ra_ab6c_q;
                  elsif rd = 1 and load_addr = x"8002AB8C" then
                    r(rd) := stack_ra_ab8c_q;
                  else
                    r(rd) := unsigned(scratch(mem_idx - SCRATCH_BASE_WORD));
                  end if;
                else
                  -- Deferred sync-BRAM load (was: r(rd) := load_word(load_addr))
                  if load_addr(31 downto 28) = x"4" then
                    dr_ra := data_rom_index(load_addr);
                    ld_src_data_q <= '1';
                    ld_rd_q <= rd;
                    ld_kind_q <= LD_WORD;
                    state_q <= S_LOAD;
                  elsif load_addr(31 downto 28) = x"8" then
                    rom_ra_a := word_index(load_addr);
                    ld_src_data_q <= '0';
                    ld_rd_q <= rd;
                    ld_kind_q <= LD_WORD;
                    state_q <= S_LOAD;
                  else
                    r(rd) := unsigned(scratch(mem_idx - SCRATCH_BASE_WORD));
                  end if;
                end if;
              end if;
            elsif h(15 downto 13) = "100" then
              rd := to_integer(unsigned(h(11 downto 7)));
              rs2 := to_integer(unsigned(h(6 downto 2)));
              if h(12) = '0' then
                if rs2 = 0 then
                  pc_next := r(rd);
                elsif rd /= 0 then
                  r(rd) := r(rs2);
                end if;
              else
                if rd /= 0 then
                  pc_next := r(rd);
                  r(1) := pc_q + 2;
                end if;
              end if;
            elsif h(15 downto 13) = "110" then
              rs2 := to_integer(unsigned(h(6 downto 2)));
              eff := r(2) + c_swsp_imm(h);
              mem_idx := word_index(eff);
              if mem_idx < ROM_WORDS then
                rom_we := true;
                rom_wa := mem_idx;
                rom_wd := std_logic_vector(r(rs2));
              elsif mem_idx >= SCRATCH_BASE_WORD and mem_idx < SCRATCH_BASE_WORD + SCRATCH_WORDS then
                scratch(mem_idx - SCRATCH_BASE_WORD) <= std_logic_vector(r(rs2));
                scratch_bytes(mem_idx - SCRATCH_BASE_WORD) <= std_logic_vector(r(rs2));
              end if;
            end if;
          end if;
        else
          op := ins(6 downto 0);
          rd := to_integer(unsigned(ins(11 downto 7)));
          rs1 := to_integer(unsigned(ins(19 downto 15)));
          rs2 := to_integer(unsigned(ins(24 downto 20)));
          case op is
            when "0010011" =>
              if rd /= 0 then
                case ins(14 downto 12) is
                  when "000" => r(rd) := r(rs1) + sext(ins(31 downto 20));
                  when "111" => r(rd) := r(rs1) and sext(ins(31 downto 20));
                  when "110" => r(rd) := r(rs1) or sext(ins(31 downto 20));
                  when "010" =>
                    if signed(r(rs1)) < signed(sext(ins(31 downto 20))) then r(rd) := to_unsigned(1, 32); else r(rd) := (others => '0'); end if;
                  when "011" =>
                    if r(rs1) < sext(ins(31 downto 20)) then r(rd) := to_unsigned(1, 32); else r(rd) := (others => '0'); end if;
                  when "001" => r(rd) := shift_left(r(rs1), to_integer(unsigned(ins(24 downto 20))));
                  when "101" =>
                    if ins(30) = '1' then r(rd) := unsigned(shift_right(signed(r(rs1)), to_integer(unsigned(ins(24 downto 20)))));
                    else r(rd) := shift_right(r(rs1), to_integer(unsigned(ins(24 downto 20)))); end if;
                  when others => null;
                end case;
              end if;
            when "0110011" =>
              if rd /= 0 then
                case ins(14 downto 12) is
                  when "000" => if ins(30) = '1' then r(rd) := r(rs1) - r(rs2); else r(rd) := r(rs1) + r(rs2); end if;
                  when "001" => r(rd) := shift_left(r(rs1), to_integer(r(rs2)(4 downto 0)));
                  when "010" => if signed(r(rs1)) < signed(r(rs2)) then r(rd) := to_unsigned(1, 32); else r(rd) := (others => '0'); end if;
                  when "011" => if r(rs1) < r(rs2) then r(rd) := to_unsigned(1, 32); else r(rd) := (others => '0'); end if;
                  when "100" => r(rd) := r(rs1) xor r(rs2);
                  when "101" => if ins(30) = '1' then r(rd) := unsigned(shift_right(signed(r(rs1)), to_integer(r(rs2)(4 downto 0)))); else r(rd) := shift_right(r(rs1), to_integer(r(rs2)(4 downto 0))); end if;
                  when "110" => r(rd) := r(rs1) or r(rs2);
                  when others => r(rd) := r(rs1) and r(rs2);
                end case;
              end if;
            when "0010111" =>
              if rd /= 0 then r(rd) := pc_q + shift_left(resize(unsigned(ins(31 downto 12)), 32), 12); end if;
            when "0110111" =>
              if rd /= 0 then r(rd) := shift_left(resize(unsigned(ins(31 downto 12)), 32), 12); end if;
            when "1101111" =>
              if rd /= 0 then r(rd) := pc_q + 4; end if;
              pc_next := pc_q + sext(ins(31) & ins(19 downto 12) & ins(20) & ins(30 downto 21) & '0');
            when "1100111" =>
              pc_next := (r(rs1) + sext(ins(31 downto 20))) and x"fffffffe";
              if rd /= 0 then r(rd) := pc_q + 4; end if;
            when "1100011" =>
              eff := pc_q + sext(ins(31) & ins(7) & ins(30 downto 25) & ins(11 downto 8) & '0');
              case ins(14 downto 12) is
                when "000" => if r(rs1) = r(rs2) then pc_next := eff; end if;
                when "001" => if r(rs1) /= r(rs2) then pc_next := eff; end if;
                when "100" => if signed(r(rs1)) < signed(r(rs2)) then pc_next := eff; end if;
                when "101" => if signed(r(rs1)) >= signed(r(rs2)) then pc_next := eff; end if;
                when "110" => if r(rs1) < r(rs2) then pc_next := eff; end if;
                when others => if r(rs1) >= r(rs2) then pc_next := eff; end if;
              end case;
            when "0000011" =>
              eff := r(rs1) + sext(ins(31 downto 20));
              if rd /= 0 then
                case ins(14 downto 12) is
                  when "000" =>
                    mem_idx := word_index(eff);
                    if mem_idx >= SCRATCH_BASE_WORD and mem_idx < SCRATCH_BASE_WORD + SCRATCH_WORDS then
                      data_w := scratch_bytes(mem_idx - SCRATCH_BASE_WORD);
                      lane := to_integer(eff(1 downto 0));
                      r(rd) := sext(data_w(lane * 8 + 7 downto lane * 8));
                    else
                      -- Deferred sync-BRAM byte load, sign-extended (was lb via load_byte)
                      if eff(31 downto 28) = x"4" then
                        dr_ra := data_rom_index(eff);
                        ld_src_data_q <= '1';
                        ld_rd_q <= rd;
                        ld_kind_q <= LD_LB;
                        ld_lane_q <= to_integer(eff(1 downto 0));
                        state_q <= S_LOAD;
                      elsif eff(31 downto 28) = x"8" then
                        rom_ra_a := word_index(eff);
                        ld_src_data_q <= '0';
                        ld_rd_q <= rd;
                        ld_kind_q <= LD_LB;
                        ld_lane_q <= to_integer(eff(1 downto 0));
                        state_q <= S_LOAD;
                      else
                        r(rd) := (others => '0');
                      end if;
                    end if;
                  when "100" =>
                    mem_idx := word_index(eff);
                    if mem_idx >= SCRATCH_BASE_WORD and mem_idx < SCRATCH_BASE_WORD + SCRATCH_WORDS then
                      data_w := scratch_bytes(mem_idx - SCRATCH_BASE_WORD);
                      lane := to_integer(eff(1 downto 0));
                      r(rd) := resize(unsigned(data_w(lane * 8 + 7 downto lane * 8)), 32);
                    else
                      -- Deferred sync-BRAM byte load, zero-extended (was lbu via load_byte)
                      if eff(31 downto 28) = x"4" then
                        dr_ra := data_rom_index(eff);
                        ld_src_data_q <= '1';
                        ld_rd_q <= rd;
                        ld_kind_q <= LD_LBU;
                        ld_lane_q <= to_integer(eff(1 downto 0));
                        state_q <= S_LOAD;
                      elsif eff(31 downto 28) = x"8" then
                        rom_ra_a := word_index(eff);
                        ld_src_data_q <= '0';
                        ld_rd_q <= rd;
                        ld_kind_q <= LD_LBU;
                        ld_lane_q <= to_integer(eff(1 downto 0));
                        state_q <= S_LOAD;
                      else
                        r(rd) := (others => '0');
                      end if;
                    end if;
                  when others =>
                    mem_idx := word_index(eff);
                    if mem_idx >= SCRATCH_BASE_WORD and mem_idx < SCRATCH_BASE_WORD + SCRATCH_WORDS then
                      r(rd) := unsigned(scratch(mem_idx - SCRATCH_BASE_WORD));
                    else
                      -- Deferred sync-BRAM word load (was: r(rd) := load_word(eff))
                      if eff(31 downto 28) = x"4" then
                        dr_ra := data_rom_index(eff);
                        ld_src_data_q <= '1';
                        ld_rd_q <= rd;
                        ld_kind_q <= LD_WORD;
                        state_q <= S_LOAD;
                      elsif eff(31 downto 28) = x"8" then
                        rom_ra_a := word_index(eff);
                        ld_src_data_q <= '0';
                        ld_rd_q <= rd;
                        ld_kind_q <= LD_WORD;
                        state_q <= S_LOAD;
                      else
                        r(rd) := (others => '0');
                      end if;
                    end if;
                end case;
              end if;
            when "0100011" =>
              eff := r(rs1) + sext(ins(31 downto 25) & ins(11 downto 7));
              if eff = UART_ADDR and ins(14 downto 12) = "000" then
                uart_shift_q <= '1' & std_logic_vector(r(rs2)(7 downto 0)) & '0';
                uart_tx_q <= '0';
                uart_busy_q <= '1';
                uart_baud_q <= 0;
                uart_bits_q <= 10;
                debug_uart_valid_next_q <= '1';
                debug_uart_byte_q <= std_logic_vector(r(rs2)(7 downto 0));
                next_pc_q <= pc_next;
                state_q <= S_UART;
              elsif eff(31 downto 28) = x"8" then
                mem_idx := word_index(eff);
                if mem_idx < ROM_WORDS then
                  -- Store to code ROM (now writable for stack spills)
                  if ins(14 downto 12) = "000" then
                    -- sb (byte store) to ROM: deferred read-modify-write.
                    -- Register the word read this edge; merge + write in S_STORE.
                    rom_ra_a := mem_idx;
                    st_idx_q <= mem_idx;
                    st_lane_q <= to_integer(eff(1 downto 0));
                    st_byte_q <= std_logic_vector(r(rs2)(7 downto 0));
                    state_q <= S_STORE;
                  else
                    -- sw (word store) to ROM
                    rom_we := true;
                    rom_wa := mem_idx;
                    rom_wd := std_logic_vector(r(rs2));
                  end if;
                elsif mem_idx >= SCRATCH_BASE_WORD and mem_idx < SCRATCH_BASE_WORD + SCRATCH_WORDS then
                  if ins(14 downto 12) = "000" then
                    data_w := scratch(mem_idx - SCRATCH_BASE_WORD);
                    lane := to_integer(eff(1 downto 0));
                    data_w(lane * 8 + 7 downto lane * 8) := std_logic_vector(r(rs2)(7 downto 0));
                    scratch(mem_idx - SCRATCH_BASE_WORD) <= data_w;
                    scratch_bytes(mem_idx - SCRATCH_BASE_WORD) <= data_w;
                  else
                    scratch(mem_idx - SCRATCH_BASE_WORD) <= std_logic_vector(r(rs2));
                    scratch_bytes(mem_idx - SCRATCH_BASE_WORD) <= std_logic_vector(r(rs2));
                  end if;
                end if;
              end if;
            when "1110011" =>
              if rd /= 0 then r(rd) := (others => '0'); end if;
            when "0101111" =>
              null;
            when others =>
              null;
          end case;
        end if;

        debug_pc_q <= std_logic_vector(pc_q(15 downto 0));
        debug_ins_q <= ins;
        debug_a0_q <= std_logic_vector(r(10)(7 downto 0));
        debug_ra_q <= std_logic_vector(r(1)(15 downto 0));
        debug_sp_q <= std_logic_vector(r(2)(15 downto 0));
        if pc_q = x"8000CD62" then
          debug_phase_q <= x"1";
        elsif pc_q = x"8000CF50" then
          debug_phase_q <= x"2";
        elsif pc_q = x"80003B8C" then
          debug_phase_q <= x"3";
        elsif pc_q = x"80003BAA" then
          debug_phase_q <= x"4";
        elsif pc_q = x"80003BBE" then
          debug_phase_q <= x"5";
        elsif pc_q = x"8000CF6E" then
          debug_phase_q <= x"6";
        end if;
        r(0) := (others => '0');
        regs_q <= r;
        if state_q = S_EXEC then
          pc_q <= pc_next;
        end if;
      end if;
    end if;
  end process;
end architecture rtl;
