-- Mailbox Testbench for RV32I CPU
-- Memory: unified 64KB at 0x80000000 (remapped internally)
-- Mailbox MMIO registers at 0x80FF0000 (debugger-independent I/O)

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use std.textio.all;
use work.rv32i_pkg.all;
use work.test_program.all;

entity tb_mailbox is
    generic (
        MAX_CYCLES : integer := 1000000
    );
end entity tb_mailbox;

architecture sim of tb_mailbox is
    constant CLK_PERIOD : time := 10 ns;
    constant MEM_WORDS  : integer := 16384;  -- 64KB

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

    -- Mailbox shadow registers
    signal mb_cmd     : std_logic_vector(31 downto 0) := (others => '0');
    signal mb_arg0    : std_logic_vector(31 downto 0) := (others => '0');
    signal mb_arg1    : std_logic_vector(31 downto 0) := (others => '0');
    signal mb_status  : std_logic_vector(31 downto 0) := (others => '0');
    signal mb_result  : std_logic_vector(31 downto 0) := (others => '0');
    signal mb_seq_id  : std_logic_vector(31 downto 0) := (others => '0');
    signal mb_trigger : std_logic_vector(31 downto 0) := (others => '0');

    -- Mailbox address decoding
    constant MB_BASE : unsigned(31 downto 0) := x"80FF0000";

    function is_mailbox_addr(addr : std_logic_vector(31 downto 0)) return boolean is
    begin
        return unsigned(addr) >= MB_BASE and
               unsigned(addr) <= (MB_BASE + x"0000001B");
    end function;

    function mb_offset(addr : std_logic_vector(31 downto 0)) return integer is
    begin
        return to_integer(unsigned(addr) - MB_BASE);
    end function;

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

    -- IMEM: remap 0x80000000 -> index by stripping high bit
    imem_data <= mem(to_integer(unsigned(imem_addr(15 downto 2))))
                 when to_integer(unsigned(imem_addr(15 downto 2))) < MEM_WORDS
                 else x"00000013";

    -- DMEM write: handle both RAM and mailbox regions
    process(clk)
        variable idx    : integer;
        variable offset : integer;
    begin
        if rising_edge(clk) then
            if dmem_we = '1' then
                if is_mailbox_addr(dmem_addr) then
                    -- Mailbox register write
                    offset := mb_offset(dmem_addr);
                    case offset is
                        when 16#00# => mb_cmd     <= dmem_wdata;
                        when 16#04# => mb_arg0    <= dmem_wdata;
                        when 16#08# => mb_arg1    <= dmem_wdata;
                        when 16#0C# => mb_status  <= dmem_wdata;
                        when 16#10# => mb_result  <= dmem_wdata;
                        when 16#14# => mb_seq_id  <= dmem_wdata;
                        when 16#18# => mb_trigger <= dmem_wdata;
                        when others => null;
                    end case;
                else
                    -- Normal RAM write
                    idx := to_integer(unsigned(dmem_addr(15 downto 2)));
                    if idx < MEM_WORDS then
                        mem(idx) <= dmem_wdata;
                    end if;
                end if;
            end if;
        end if;
    end process;

    -- DMEM read: handle both RAM and mailbox regions
    dmem_rdata <= mb_cmd    when dmem_re = '1' and is_mailbox_addr(dmem_addr) and mb_offset(dmem_addr) = 16#00# else
                  mb_arg0   when dmem_re = '1' and is_mailbox_addr(dmem_addr) and mb_offset(dmem_addr) = 16#04# else
                  mb_arg1   when dmem_re = '1' and is_mailbox_addr(dmem_addr) and mb_offset(dmem_addr) = 16#08# else
                  mb_status when dmem_re = '1' and is_mailbox_addr(dmem_addr) and mb_offset(dmem_addr) = 16#0C# else
                  mb_result when dmem_re = '1' and is_mailbox_addr(dmem_addr) and mb_offset(dmem_addr) = 16#10# else
                  mb_seq_id when dmem_re = '1' and is_mailbox_addr(dmem_addr) and mb_offset(dmem_addr) = 16#14# else
                  mb_trigger when dmem_re = '1' and is_mailbox_addr(dmem_addr) and mb_offset(dmem_addr) = 16#18# else
                  mem(to_integer(unsigned(dmem_addr(15 downto 2))))
                      when dmem_re = '1' and to_integer(unsigned(dmem_addr(15 downto 2))) < MEM_WORDS else
                  (others => '0');

    -- Test driver + mailbox command dispatch
    process
        variable cycles   : integer := 0;
        variable ch_val   : integer;
        variable out_line : line;
        variable sentinel : std_logic_vector(31 downto 0);
        constant SENTINEL_IDX : integer := 16#8000# / 4;  -- 0x80008000 relative to RAM base
    begin
        reset_n <= '0';
        wait for CLK_PERIOD * 5;
        reset_n <= '1';

        while not done and cycles < MAX_CYCLES loop
            wait until falling_edge(clk);
            cycles := cycles + 1;

            -- Check if trigger was just written with magic value
            if mb_trigger = MB_TRIGGER_MAGIC then
                -- Dispatch based on command
                if mb_cmd = MB_CMD_PUTC then
                    ch_val := to_integer(unsigned(mb_arg0(7 downto 0)));
                    if ch_val >= 32 and ch_val < 127 then
                        write(out_line, character'val(ch_val));
                    elsif ch_val = 10 then
                        write(out_line, string'("\n"));
                    end if;

                elsif mb_cmd = MB_CMD_EXIT then
                    -- Write sentinel: 0xCAFE0000 | exit_code[15:0]
                    sentinel := MB_SENTINEL_SUCCESS or
                                (x"0000" & mb_arg0(15 downto 0));
                    mem(SENTINEL_IDX) <= sentinel;
                    report "SENTINEL: 0x" & to_hstring(unsigned(sentinel));
                    report "EXIT_CODE: " & integer'image(to_integer(unsigned(mb_arg0)));
                    done <= true;

                elsif mb_cmd = MB_CMD_RESULT then
                    report "RESULT: pass=" & integer'image(to_integer(unsigned(mb_arg0))) &
                           " value=" & integer'image(to_integer(unsigned(mb_arg1)));
                end if;

                -- Clear trigger after processing
                mb_trigger <= (others => '0');
            end if;
        end loop;

        -- Timeout handling
        if not done then
            mem(SENTINEL_IDX) <= MB_SENTINEL_TIMEOUT;
            report "SENTINEL: 0x" & to_hstring(unsigned(MB_SENTINEL_TIMEOUT));
            report "TIMEOUT after " & integer'image(cycles) & " cycles";
            done <= true;
        end if;

        report "CYCLES: " & integer'image(cycles);

        if out_line /= null then
            report "OUTPUT: " & out_line.all;
        else
            report "OUTPUT: (empty)";
        end if;

        wait;
    end process;
end architecture sim;
