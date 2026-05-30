library ieee;
use ieee.std_logic_1164.all;

library unisim;
use unisim.vcomponents.all;

entity mlk_s02_100t_addition_bscan_demo_top is
end entity mlk_s02_100t_addition_bscan_demo_top;

architecture rtl of mlk_s02_100t_addition_bscan_demo_top is
    signal capture : std_logic;
    signal shift   : std_logic;
    signal tck     : std_logic;
    signal tdi     : std_logic;
    signal tdo     : std_logic;
    signal sel     : std_logic;
    signal sum     : std_logic_vector(4 downto 0);
    signal shreg   : std_logic_vector(7 downto 0) := (others => '0');

    attribute keep : string;
    attribute keep of sum   : signal is "true";
    attribute keep of shreg : signal is "true";
begin
    u_add : entity work.addition_demo
        port map (
            a   => "0011",
            b   => "0101",
            sum => sum
        );

    u_bscan : BSCANE2
        generic map (
            JTAG_CHAIN => 1
        )
        port map (
            CAPTURE => capture,
            DRCK    => open,
            RESET   => open,
            RUNTEST => open,
            SEL     => sel,
            SHIFT   => shift,
            TCK     => tck,
            TDI     => tdi,
            TMS     => open,
            UPDATE  => open,
            TDO     => tdo
        );

    process (tck)
    begin
        if rising_edge(tck) then
            if capture = '1' then
                shreg <= "000" & sum;
            elsif sel = '1' and shift = '1' then
                shreg <= tdi & shreg(7 downto 1);
            end if;
        end if;
    end process;

    tdo <= shreg(0) when sel = '1' else '0';
end architecture rtl;
