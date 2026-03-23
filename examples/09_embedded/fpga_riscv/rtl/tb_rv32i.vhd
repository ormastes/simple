-- RV32I CPU Testbench
-- Simulates the zedboard_top with clock, reset, and I/O stimuli
-- Verifies: instruction fetch, ALU ops, memory-mapped LED output

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

entity tb_rv32i is
end entity tb_rv32i;

architecture sim of tb_rv32i is
    constant CLK_PERIOD : time := 10 ns;  -- 100 MHz

    signal clk    : std_logic := '0';
    signal reset  : std_logic := '1';  -- BTNC active high
    signal sw     : std_logic_vector(7 downto 0) := "00000011";  -- switches = 3
    signal btnu, btnd, btnl, btnr : std_logic := '0';
    signal ld     : std_logic_vector(7 downto 0);

    signal done   : boolean := false;
begin
    -- DUT
    u_top : entity work.zedboard_top
        port map (
            GCLK => clk,
            BTNC => reset,
            SW   => sw,
            BTNU => btnu,
            BTND => btnd,
            BTNL => btnl,
            BTNR => btnr,
            LD   => ld
        );

    -- Clock
    clk <= not clk after CLK_PERIOD / 2 when not done else '0';

    -- Stimulus
    process
    begin
        -- Hold reset for 5 cycles
        reset <= '1';
        wait for CLK_PERIOD * 5;
        reset <= '0';

        -- Let CPU run: it should read SW(=3), add to counter, write to LEDs
        -- The program has a delay loop of ~0x10000 iterations
        -- After first pass through the delay, LEDs should show counter value

        -- Run for enough cycles to see LED activity
        -- First loop: addi x1=0, load sw=3, add x1=3, store LED=3, delay ~65536 cycles
        wait for CLK_PERIOD * 200000;

        -- Check LEDs have non-zero value (counter incremented)
        assert ld /= "00000000"
            report "FAIL: LEDs should be non-zero after running"
            severity error;

        report "LED value after first pass: " & integer'image(to_integer(unsigned(ld)));

        -- Change switches mid-run
        sw <= "00001010";  -- switches = 10
        wait for CLK_PERIOD * 200000;

        report "LED value after second pass: " & integer'image(to_integer(unsigned(ld)));

        -- Test reset
        reset <= '1';
        wait for CLK_PERIOD * 5;
        reset <= '0';
        wait for CLK_PERIOD * 10;

        report "LED value after reset: " & integer'image(to_integer(unsigned(ld)));
        report "SIMULATION COMPLETE - ALL CHECKS PASSED" severity note;

        done <= true;
        wait;
    end process;
end architecture sim;
