-- jtag_tap.vhd — IEEE 1149.1 JTAG TAP controller (Stage 1 of RISC-V JTAG debug)
--
-- Full 16-state TAP FSM, 5-bit instruction register, on-chip IDCODE and BYPASS
-- data registers, and an external-DR interface used by the RISC-V DTM
-- (riscv_dtm.vhd) for the DTMCS and DMI registers.
--
-- IDCODE literal: 0x15350067
--   version (31:28) = 0x1
--   part    (27:12) = 0x5350  ("SP" in ASCII — Simple Project)
--   manuf   (11:1)  = 0x033   (11-bit JEDEC-shaped placeholder id)
--   bit 0           = '1'     (mandatory IEEE 1149.1 LSB)
--
-- RTL conventions (documented for the testbench and DTM):
--   * State register and all capture/shift/update actions occur on the RISING
--     edge of TCK, keyed on the state held BEFORE that edge (so the edge that
--     leaves Capture-DR performs the capture, each rising edge spent in
--     Shift-DR shifts once, and the edge that leaves Update-DR performs the
--     update). This matches IEEE 1149.1 observable behaviour at the pins.
--   * TDO is registered on the FALLING edge of TCK from the serial output of
--     the currently selected register, per IEEE 1149.1.
--   * capture_en / shift_en / update_en are combinational decodes of the
--     current state; the DTM performs its own register actions on the same
--     rising edges the TAP would.
--   * TRST_n is an asynchronous reset for the TAP itself; DM-side paths in
--     later stages remain synchronous.

library ieee;
use ieee.std_logic_1164.all;

entity jtag_tap is
  generic (
    IDCODE_VALUE : std_logic_vector(31 downto 0) := x"15350067"
  );
  port (
    tck    : in  std_logic;
    tms    : in  std_logic;
    tdi    : in  std_logic;
    trst_n : in  std_logic;
    tdo    : out std_logic;

    -- Debug/test visibility: '1' while the FSM is in Test-Logic-Reset.
    tlr_o  : out std_logic;

    -- External data-register interface (RISC-V DTM: DTMCS / DMI)
    sel_dtmcs  : out std_logic;  -- current instruction is DTMCS
    sel_dmi    : out std_logic;  -- current instruction is DMI
    capture_en : out std_logic;  -- state = Capture-DR
    shift_en   : out std_logic;  -- state = Shift-DR
    update_en  : out std_logic;  -- state = Update-DR
    dr_tdi     : out std_logic;  -- serial data into external shift registers
    dtmcs_tdo  : in  std_logic;  -- serial out of the DTM's DTMCS shift reg
    dmi_tdo    : in  std_logic   -- serial out of the DTM's DMI shift reg
  );
end entity jtag_tap;

architecture rtl of jtag_tap is

  type tap_state_t is (
    S_TEST_LOGIC_RESET, S_RUN_TEST_IDLE,
    S_SELECT_DR, S_CAPTURE_DR, S_SHIFT_DR, S_EXIT1_DR,
    S_PAUSE_DR, S_EXIT2_DR, S_UPDATE_DR,
    S_SELECT_IR, S_CAPTURE_IR, S_SHIFT_IR, S_EXIT1_IR,
    S_PAUSE_IR, S_EXIT2_IR, S_UPDATE_IR
  );

  -- Instruction encodings (RISC-V Debug Spec v0.13 Table 6.1 conventions)
  constant INSN_IDCODE : std_logic_vector(4 downto 0) := "00001";  -- 0x01
  constant INSN_DTMCS  : std_logic_vector(4 downto 0) := "10000";  -- 0x10
  constant INSN_DMI    : std_logic_vector(4 downto 0) := "10001";  -- 0x11
  constant INSN_BYPASS : std_logic_vector(4 downto 0) := "11111";  -- 0x1F
  -- All other encodings decode to BYPASS (IEEE 1149.1 requirement).

  signal state     : tap_state_t := S_TEST_LOGIC_RESET;
  signal ir        : std_logic_vector(4 downto 0) := INSN_IDCODE;
  signal ir_sr     : std_logic_vector(4 downto 0) := (others => '0');
  signal idcode_sr : std_logic_vector(31 downto 0) := (others => '0');
  signal bypass_sr : std_logic := '0';
  signal tdo_r     : std_logic := '0';

begin

  ----------------------------------------------------------------------------
  -- State machine + instruction register + on-chip data registers.
  -- Actions keyed on the state held before each rising edge.
  ----------------------------------------------------------------------------
  process (tck, trst_n)
  begin
    if trst_n = '0' then
      state     <= S_TEST_LOGIC_RESET;
      ir        <= INSN_IDCODE;
      ir_sr     <= (others => '0');
      idcode_sr <= (others => '0');
      bypass_sr <= '0';
    elsif rising_edge(tck) then

      -- Register actions in the current state -------------------------------
      case state is
        when S_TEST_LOGIC_RESET =>
          ir <= INSN_IDCODE;  -- IEEE 1149.1: IR resets to IDCODE (when present)

        when S_CAPTURE_IR =>
          ir_sr <= "00001";   -- mandatory "...01" capture pattern

        when S_SHIFT_IR =>
          ir_sr <= tdi & ir_sr(4 downto 1);

        when S_UPDATE_IR =>
          ir <= ir_sr;

        when S_CAPTURE_DR =>
          if ir = INSN_IDCODE then
            idcode_sr <= IDCODE_VALUE;
          elsif ir /= INSN_DTMCS and ir /= INSN_DMI then
            bypass_sr <= '0';  -- BYPASS captures '0'
          end if;

        when S_SHIFT_DR =>
          if ir = INSN_IDCODE then
            idcode_sr <= tdi & idcode_sr(31 downto 1);
          elsif ir /= INSN_DTMCS and ir /= INSN_DMI then
            bypass_sr <= tdi;  -- 1-bit passthrough
          end if;

        when others =>
          null;
      end case;

      -- State transitions ---------------------------------------------------
      case state is
        when S_TEST_LOGIC_RESET =>
          if tms = '0' then state <= S_RUN_TEST_IDLE; end if;
        when S_RUN_TEST_IDLE =>
          if tms = '1' then state <= S_SELECT_DR; end if;
        when S_SELECT_DR =>
          if tms = '1' then state <= S_SELECT_IR;
          else state <= S_CAPTURE_DR; end if;
        when S_CAPTURE_DR =>
          if tms = '1' then state <= S_EXIT1_DR;
          else state <= S_SHIFT_DR; end if;
        when S_SHIFT_DR =>
          if tms = '1' then state <= S_EXIT1_DR; end if;
        when S_EXIT1_DR =>
          if tms = '1' then state <= S_UPDATE_DR;
          else state <= S_PAUSE_DR; end if;
        when S_PAUSE_DR =>
          if tms = '1' then state <= S_EXIT2_DR; end if;
        when S_EXIT2_DR =>
          if tms = '1' then state <= S_UPDATE_DR;
          else state <= S_SHIFT_DR; end if;
        when S_UPDATE_DR =>
          if tms = '1' then state <= S_SELECT_DR;
          else state <= S_RUN_TEST_IDLE; end if;
        when S_SELECT_IR =>
          if tms = '1' then state <= S_TEST_LOGIC_RESET;
          else state <= S_CAPTURE_IR; end if;
        when S_CAPTURE_IR =>
          if tms = '1' then state <= S_EXIT1_IR;
          else state <= S_SHIFT_IR; end if;
        when S_SHIFT_IR =>
          if tms = '1' then state <= S_EXIT1_IR; end if;
        when S_EXIT1_IR =>
          if tms = '1' then state <= S_UPDATE_IR;
          else state <= S_PAUSE_IR; end if;
        when S_PAUSE_IR =>
          if tms = '1' then state <= S_EXIT2_IR; end if;
        when S_EXIT2_IR =>
          if tms = '1' then state <= S_UPDATE_IR;
          else state <= S_SHIFT_IR; end if;
        when S_UPDATE_IR =>
          if tms = '1' then state <= S_SELECT_DR;
          else state <= S_RUN_TEST_IDLE; end if;
      end case;

    end if;
  end process;

  ----------------------------------------------------------------------------
  -- TDO: registered on the falling edge from the selected serial output.
  ----------------------------------------------------------------------------
  process (tck)
  begin
    if falling_edge(tck) then
      if state = S_SHIFT_IR then
        tdo_r <= ir_sr(0);
      elsif state = S_SHIFT_DR then
        if ir = INSN_IDCODE then
          tdo_r <= idcode_sr(0);
        elsif ir = INSN_DTMCS then
          tdo_r <= dtmcs_tdo;
        elsif ir = INSN_DMI then
          tdo_r <= dmi_tdo;
        else
          tdo_r <= bypass_sr;
        end if;
      end if;
    end if;
  end process;

  tdo <= tdo_r;

  ----------------------------------------------------------------------------
  -- Combinational decodes for the external DTM.
  ----------------------------------------------------------------------------
  tlr_o      <= '1' when state = S_TEST_LOGIC_RESET else '0';
  sel_dtmcs  <= '1' when ir = INSN_DTMCS else '0';
  sel_dmi    <= '1' when ir = INSN_DMI else '0';
  capture_en <= '1' when state = S_CAPTURE_DR else '0';
  shift_en   <= '1' when state = S_SHIFT_DR else '0';
  update_en  <= '1' when state = S_UPDATE_DR else '0';
  dr_tdi     <= tdi;

end architecture rtl;
