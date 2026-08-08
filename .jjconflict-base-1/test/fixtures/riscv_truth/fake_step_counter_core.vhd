library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

-- Deliberate-red fixture for scripts/check/check-riscv-rtl-truth.shs.
--
-- This is a hand-crafted reproduction of the "smoke_handoff" landmine
-- documented in .spipe/rv64-ghdl-fpga-boot/state.md (D-2): a hardcoded
-- step counter that bit-bangs a fixed UART byte sequence instead of
-- fetching/decoding/executing real RISC-V instructions. There is no
-- opcode case/if over an instruction field anywhere in this file.
--
-- The truth checker MUST reject this file when pointed at this fixture
-- directory (rule 2: scripted step-counter core; rule 3: no instruction
-- decode). If the checker ever passes this fixture, the checker itself is
-- broken and must not be trusted.

entity fake_step_counter_core is
  port (
    clk : in std_logic;
    rst : in std_logic;
    uart_tx : out std_logic
  );
end entity fake_step_counter_core;

architecture smoke_handoff of fake_step_counter_core is
  signal step : integer range 0 to 3 := 0;
  signal uart_tx_q : std_logic := '1';
begin
  uart_tx <= uart_tx_q;

  process(clk)
  begin
    if rising_edge(clk) then
      if rst = '1' then
        step <= 0;
      else
        -- Predetermined output selected purely by a step counter: no
        -- instruction fetch, no decode, no register file, no ALU.
        case step is
          when 0 =>
            uart_tx_q <= '0';
          when 1 =>
            uart_tx_q <= '1';
          when 2 =>
            uart_tx_q <= '0';
          when others =>
            uart_tx_q <= '1';
        end case;
        step <= step + 1;
      end if;
    end if;
  end process;
end architecture smoke_handoff;
