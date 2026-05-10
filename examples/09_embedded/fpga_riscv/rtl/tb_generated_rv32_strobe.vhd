library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use work.simple_rv32i_core_pkg.all;
use work.test_program.all;

entity tb_generated_rv32_strobe is
    generic (
        MAX_CYCLES : integer := 200000
    );
end entity tb_generated_rv32_strobe;

architecture sim of tb_generated_rv32_strobe is
    constant CLK_PERIOD : time := 10 ns;
    constant MEM_WORDS  : integer := 16384;
    constant PASS_ADDR_IDX : integer := 16#100# / 4;
    constant FAIL_ADDR_IDX : integer := 16#104# / 4;

    signal clk        : std_logic := '0';
    signal reset_n    : std_logic := '0';
    signal imem_addr  : std_logic_vector(31 downto 0);
    signal imem_data  : std_logic_vector(31 downto 0);
    signal dmem_addr  : std_logic_vector(31 downto 0);
    signal dmem_wdata : std_logic_vector(31 downto 0);
    signal dmem_rdata : std_logic_vector(31 downto 0);
    signal dmem_we    : std_logic;
    signal dmem_re    : std_logic;
    signal dmem_width : std_logic_vector(1 downto 0);
    signal dmem_wstrb : std_logic_vector(3 downto 0);
    signal irq_software : std_logic := '0';
    signal irq_timer    : std_logic := '0';
    signal irq_external : std_logic := '0';
    signal debug_pc   : std_logic_vector(31 downto 0);
    signal semi_trigger : std_logic;
    signal semi_op    : std_logic_vector(31 downto 0);
    signal semi_param : std_logic_vector(31 downto 0);
    signal trap       : std_logic;
    signal halt       : std_logic;

    type mem_t is array (0 to MEM_WORDS - 1) of std_logic_vector(31 downto 0);

    function init_mem return mem_t is
        variable m : mem_t := (others => x"00000013");
    begin
        for i in 0 to PROGRAM_SIZE - 1 loop
            m(i) := PROGRAM_DATA(i);
        end loop;
        return m;
    end function;

    signal mem : mem_t := init_mem;
    signal done : boolean := false;
begin
    u_cpu : entity work.simple_rv32gc_core
        port map (
            clk        => clk,
            reset_n    => reset_n,
            imem_addr  => imem_addr,
            imem_rdata => imem_data,
            dmem_addr  => dmem_addr,
            dmem_wdata => dmem_wdata,
            dmem_rdata => dmem_rdata,
            dmem_we    => dmem_we,
            dmem_re    => dmem_re,
            dmem_width => dmem_width,
            dmem_wstrb => dmem_wstrb,
            irq_software => irq_software,
            irq_timer  => irq_timer,
            irq_external => irq_external,
            mmu_dmem_l2_pte => (others => '0'),
            mmu_dmem_l1_pte => (others => '0'),
            mmu_dmem_l0_pte => (others => '0'),
            debug_pc   => debug_pc,
            semi_trigger => semi_trigger,
            semi_op    => semi_op,
            semi_param => semi_param,
            trap       => trap,
            halt       => halt
        );

    clk <= not clk after CLK_PERIOD / 2 when not done else '0';

    imem_data <= mem(to_integer(unsigned(imem_addr(15 downto 2))))
        when to_integer(unsigned(imem_addr(15 downto 2))) < MEM_WORDS
        else x"00000013";

    process(clk)
        variable idx : integer;
        variable current_word : std_logic_vector(31 downto 0);
    begin
        if rising_edge(clk) then
            if dmem_we = '1' then
                idx := to_integer(unsigned(dmem_addr(15 downto 2)));
                if idx < MEM_WORDS then
                    current_word := mem(idx);
                    if dmem_wstrb(0) = '1' then
                        current_word(7 downto 0) := dmem_wdata(7 downto 0);
                    end if;
                    if dmem_wstrb(1) = '1' then
                        current_word(15 downto 8) := dmem_wdata(15 downto 8);
                    end if;
                    if dmem_wstrb(2) = '1' then
                        current_word(23 downto 16) := dmem_wdata(23 downto 16);
                    end if;
                    if dmem_wstrb(3) = '1' then
                        current_word(31 downto 24) := dmem_wdata(31 downto 24);
                    end if;
                    mem(idx) <= current_word;
                end if;
            end if;
        end if;
    end process;

    dmem_rdata <= mem(to_integer(unsigned(dmem_addr(15 downto 2))))
        when to_integer(unsigned(dmem_addr(15 downto 2))) < MEM_WORDS
        else (others => '0');

    process
        variable cycles : integer := 0;
        variable pass_value : integer;
        variable fail_value : integer;
    begin
        reset_n <= '0';
        wait for CLK_PERIOD * 5;
        reset_n <= '1';

        while halt = '0' and trap = '0' and cycles < MAX_CYCLES loop
            wait for CLK_PERIOD;
            cycles := cycles + 1;
        end loop;

        pass_value := to_integer(unsigned(mem(PASS_ADDR_IDX)));
        fail_value := to_integer(unsigned(mem(FAIL_ADDR_IDX)));
        report "CYCLES: " & integer'image(cycles);
        report "PASS_WORD: " & integer'image(pass_value);
        report "FAIL_WORD: " & integer'image(fail_value);
        if halt = '1' and pass_value = 42 and fail_value = 0 then
            report "GENERATED_RV32_STROBE: PASS";
        else
            report "GENERATED_RV32_STROBE: FAIL";
        end if;
        done <= true;
        wait;
    end process;
end architecture sim;
