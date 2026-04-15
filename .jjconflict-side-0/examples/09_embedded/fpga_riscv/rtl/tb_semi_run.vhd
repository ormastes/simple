-- Semihosting test runner — loads program from test_program package
library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use std.textio.all;
use work.rv32i_pkg.all;
use work.test_program.all;

entity tb_semi_run is
end entity tb_semi_run;

architecture sim of tb_semi_run is
    constant CLK_PERIOD : time := 10 ns;
    constant MEM_WORDS  : integer := 16384;

    signal clk     : std_logic := '0';
    signal reset_n : std_logic := '0';
    signal imem_addr, dmem_addr     : std_logic_vector(31 downto 0);
    signal imem_data, dmem_wdata    : std_logic_vector(31 downto 0);
    signal dmem_rdata               : std_logic_vector(31 downto 0);
    signal dmem_we, dmem_re         : std_logic;
    signal dmem_width               : std_logic_vector(1 downto 0);
    signal halted                   : std_logic;
    signal semi_trigger             : std_logic;
    signal semi_op, semi_param      : std_logic_vector(31 downto 0);

    type mem_t is array (0 to MEM_WORDS-1) of std_logic_vector(31 downto 0);

    -- Initialize memory from program package
    function init_mem return mem_t is
        variable m : mem_t := (others => x"00000013");
    begin
        for i in 0 to PROGRAM_SIZE-1 loop
            m(i) := PROGRAM_DATA(i);
        end loop;
        return m;
    end function;

    signal mem : mem_t := init_mem;
    signal done : boolean := false;
begin
    u_cpu : entity work.rv32i_core
        generic map (RESET_ADDR => x"80000000")
        port map (
            clk=>clk, reset_n=>reset_n,
            imem_addr=>imem_addr, imem_data=>imem_data,
            dmem_addr=>dmem_addr, dmem_wdata=>dmem_wdata,
            dmem_rdata=>dmem_rdata, dmem_we=>dmem_we,
            dmem_re=>dmem_re, dmem_width=>dmem_width,
            halted=>halted,
            semi_trigger=>semi_trigger, semi_op=>semi_op, semi_param=>semi_param
        );

    clk <= not clk after CLK_PERIOD/2 when not done else '0';

    -- Memory: address bits 15:2 index into array (strip 0x80000000 high bit)
    imem_data <= mem(to_integer(unsigned(imem_addr(15 downto 2))))
                 when to_integer(unsigned(imem_addr(15 downto 2))) < MEM_WORDS
                 else x"00000013";

    process(clk)
        variable idx : integer;
    begin
        if rising_edge(clk) then
            if dmem_we = '1' then
                idx := to_integer(unsigned(dmem_addr(15 downto 2)));
                if idx < MEM_WORDS then
                    mem(idx) <= dmem_wdata;
                end if;
            end if;
        end if;
    end process;

    dmem_rdata <= mem(to_integer(unsigned(dmem_addr(15 downto 2))))
                  when dmem_re = '1' and to_integer(unsigned(dmem_addr(15 downto 2))) < MEM_WORDS
                  else (others => '0');

    -- Test driver + semihosting
    process
        variable cycles    : integer := 0;
        variable str_addr  : unsigned(15 downto 0);
        variable ch_val    : integer;
        variable word_val  : std_logic_vector(31 downto 0);
        variable byte_off  : integer;
        variable idx       : integer;
        variable out_line  : line;
    begin
        reset_n <= '0';
        wait for CLK_PERIOD * 5;
        reset_n <= '1';

        while halted = '0' and cycles < 500000 loop
            wait until falling_edge(clk);
            cycles := cycles + 1;

            if semi_trigger = '1' then
                if semi_op = SYS_WRITE0 then
                    str_addr := unsigned(semi_param(15 downto 0));
                    for i in 0 to 1023 loop
                        idx := to_integer(str_addr(15 downto 2));
                        if idx < MEM_WORDS then
                            word_val := mem(idx);
                        else
                            word_val := (others => '0');
                        end if;
                        byte_off := to_integer(str_addr(1 downto 0));
                        case byte_off is
                            when 0 => ch_val := to_integer(unsigned(word_val(7 downto 0)));
                            when 1 => ch_val := to_integer(unsigned(word_val(15 downto 8)));
                            when 2 => ch_val := to_integer(unsigned(word_val(23 downto 16)));
                            when 3 => ch_val := to_integer(unsigned(word_val(31 downto 24)));
                            when others => ch_val := 0;
                        end case;
                        exit when ch_val = 0;
                        if ch_val >= 32 and ch_val < 127 then
                            write(out_line, character'val(ch_val));
                        elsif ch_val = 10 then
                            write(out_line, string'("\n"));
                        end if;
                        str_addr := str_addr + 1;
                    end loop;
                end if;
            end if;
        end loop;

        report "CYCLES: " & integer'image(cycles);
        report "EXIT_CODE: " & integer'image(to_integer(unsigned(semi_param)));

        if out_line /= null then
            report "OUTPUT: " & out_line.all;
        else
            report "OUTPUT: (empty)";
        end if;

        done <= true;
        wait;
    end process;
end architecture sim;
