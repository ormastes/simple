-- MLK-S02-100T wrapper scaffold
--
-- Status:
-- - logical interface scaffold only
-- - not wired to verified pins
-- - not wired to a verified generated or handwritten core instance
--
-- Purpose:
-- - preserve the board-level port contract for future synthesis work
-- - keep wrapper naming aligned with config/resources/boards/mlk_s02_100t.sdn
-- - provide a minimal starting point once the real XDC is available

library ieee;
use ieee.std_logic_1164.all;

entity mlk_s02_100t_wrapper_stub is
    port (
        clk25   : in  std_logic;
        rst_n   : in  std_logic;
        uart_tx : out std_logic;
        uart_rx : in  std_logic;
        led     : out std_logic_vector(7 downto 0);
        btn     : in  std_logic_vector(3 downto 0)
    );
end entity mlk_s02_100t_wrapper_stub;

architecture rtl of mlk_s02_100t_wrapper_stub is
begin
    -- Safe placeholder behavior only.
    -- Replace with a real core/top-level integration after the verified XDC
    -- and board-level memory/UART/reset wiring are available.
    uart_tx <= '1';
    led <= (others => '0');
end architecture rtl;
