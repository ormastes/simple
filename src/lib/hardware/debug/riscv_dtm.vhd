-- riscv_dtm.vhd — RISC-V Debug Transport Module (Debug Spec v0.13 §6)
--
-- Implements the DTMCS and DMI JTAG data registers behind the TAP's
-- external-DR interface (see jtag_tap.vhd) and masters the DMI bus
-- (see dmi_bus.vhd).
--
-- DTMCS (32 bits, v0.13 §6.1.4):
--   [3:0]   version      = 1  (spec v0.13)
--   [9:4]   abits        = 7
--   [11:10] dmistat      (0 = no error, 2 = failed, 3 = busy; sticky)
--   [14:12] idle         = 1  (hint: 1 Run-Test/Idle cycle between scans)
--   [16]    dmireset     (W1: clears sticky dmistat)
--   [17]    dmihardreset (W1: aborts any DMI transaction, clears state)
--   others  0
--
-- DMI (abits+34 = 41 bits, v0.13 §6.1.5): { address[40:34], data[33:2], op[1:0] }
--   op written: 0 = nop, 1 = read, 2 = write
--   op captured: 0 = success, 2 = failed, 3 = busy
--
-- Everything runs in the TCK domain (Stage 1: no CDC yet — the DMI bus and
-- register file are also clocked by TCK). Register actions occur on rising
-- TCK edges gated by the TAP's capture/shift/update strobes, matching the
-- TAP's own convention.

library ieee;
use ieee.std_logic_1164.all;

entity riscv_dtm is
  port (
    tck    : in  std_logic;
    trst_n : in  std_logic;

    -- TAP external-DR interface
    tlr        : in  std_logic;  -- TAP in Test-Logic-Reset
    sel_dtmcs  : in  std_logic;
    sel_dmi    : in  std_logic;
    capture_en : in  std_logic;
    shift_en   : in  std_logic;
    update_en  : in  std_logic;
    tdi        : in  std_logic;
    dtmcs_tdo  : out std_logic;
    dmi_tdo    : out std_logic;

    -- DMI bus master
    dmi_valid : out std_logic;
    dmi_addr  : out std_logic_vector(6 downto 0);
    dmi_wdata : out std_logic_vector(31 downto 0);
    dmi_op    : out std_logic_vector(1 downto 0);
    dmi_rdata : in  std_logic_vector(31 downto 0);
    dmi_resp  : in  std_logic_vector(1 downto 0);
    dmi_ready : in  std_logic
  );
end entity riscv_dtm;

architecture rtl of riscv_dtm is

  constant ABITS : natural := 7;

  signal dtmcs_sr : std_logic_vector(31 downto 0) := (others => '0');
  signal dmi_sr   : std_logic_vector(ABITS + 33 downto 0) := (others => '0');

  signal addr_r : std_logic_vector(6 downto 0)  := (others => '0');
  signal data_r : std_logic_vector(31 downto 0) := (others => '0');
  signal stat_r : std_logic_vector(1 downto 0)  := "00";  -- sticky dmistat
  signal busy_r : std_logic := '0';
  signal pend_r : std_logic_vector(1 downto 0)  := "00";  -- op in flight

  signal valid_r : std_logic := '0';
  signal vaddr_r : std_logic_vector(6 downto 0)  := (others => '0');
  signal vdata_r : std_logic_vector(31 downto 0) := (others => '0');
  signal vop_r   : std_logic_vector(1 downto 0)  := "00";

begin

  process (tck, trst_n)
    variable dtmcs_cap : std_logic_vector(31 downto 0);
    variable op_cap    : std_logic_vector(1 downto 0);
  begin
    if trst_n = '0' then
      dtmcs_sr <= (others => '0');
      dmi_sr   <= (others => '0');
      addr_r   <= (others => '0');
      data_r   <= (others => '0');
      stat_r   <= "00";
      busy_r   <= '0';
      pend_r   <= "00";
      valid_r  <= '0';
      vaddr_r  <= (others => '0');
      vdata_r  <= (others => '0');
      vop_r    <= "00";
    elsif rising_edge(tck) then
      valid_r <= '0';  -- single-cycle request pulse

      -- DMI bus completion
      if busy_r = '1' and dmi_ready = '1' then
        busy_r <= '0';
        if pend_r = "01" then
          data_r <= dmi_rdata;
        end if;
        if dmi_resp /= "00" then
          stat_r <= dmi_resp;  -- sticky error
        end if;
      end if;

      if tlr = '1' then
        stat_r <= "00";  -- Test-Logic-Reset clears sticky status
      end if;

      -- DTMCS scan
      if sel_dtmcs = '1' then
        if capture_en = '1' then
          dtmcs_cap := (others => '0');
          dtmcs_cap(3 downto 0)  := "0001";    -- version = 1 (spec 0.13)
          dtmcs_cap(9 downto 4)  := "000111";  -- abits = 7
          if busy_r = '1' then
            dtmcs_cap(11 downto 10) := "11";
          else
            dtmcs_cap(11 downto 10) := stat_r;
          end if;
          dtmcs_cap(14 downto 12) := "001";    -- idle hint = 1
          dtmcs_sr <= dtmcs_cap;
        elsif shift_en = '1' then
          dtmcs_sr <= tdi & dtmcs_sr(31 downto 1);
        elsif update_en = '1' then
          if dtmcs_sr(17) = '1' then           -- dmihardreset
            stat_r <= "00";
            busy_r <= '0';
            pend_r <= "00";
          elsif dtmcs_sr(16) = '1' then        -- dmireset
            stat_r <= "00";
          end if;
        end if;
      end if;

      -- DMI scan
      if sel_dmi = '1' then
        if capture_en = '1' then
          if busy_r = '1' then
            op_cap := "11";
            stat_r <= "11";  -- capture while busy sets sticky busy
          else
            op_cap := stat_r;
          end if;
          dmi_sr <= addr_r & data_r & op_cap;
        elsif shift_en = '1' then
          dmi_sr <= tdi & dmi_sr(dmi_sr'high downto 1);
        elsif update_en = '1' then
          if busy_r = '1' then
            stat_r <= "11";  -- new request while busy: sticky busy
          elsif stat_r = "00" then
            case dmi_sr(1 downto 0) is
              when "01" | "10" =>              -- read | write
                valid_r <= '1';
                vaddr_r <= dmi_sr(ABITS + 33 downto 34);
                vdata_r <= dmi_sr(33 downto 2);
                vop_r   <= dmi_sr(1 downto 0);
                pend_r  <= dmi_sr(1 downto 0);
                busy_r  <= '1';
                addr_r  <= dmi_sr(ABITS + 33 downto 34);
                if dmi_sr(1 downto 0) = "10" then
                  data_r <= dmi_sr(33 downto 2);
                end if;
              when others =>                   -- nop
                null;
            end case;
          end if;
        end if;
      end if;
    end if;
  end process;

  dtmcs_tdo <= dtmcs_sr(0);
  dmi_tdo   <= dmi_sr(0);

  dmi_valid <= valid_r;
  dmi_addr  <= vaddr_r;
  dmi_wdata <= vdata_r;
  dmi_op    <= vop_r;

end architecture rtl;
