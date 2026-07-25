library ieee;
use ieee.std_logic_1164.all;

-- Deliberate-red fixture for scripts/check/check-riscv-rtl-truth.shs, rule 4
-- (dangling `entity work.NAME` instantiation).
--
-- Companion to fake_step_counter_core.vhd (rules 2/3). This file proves rule
-- 4 still fires on a GENUINELY undefined entity after the entity-definition
-- lookup was widened to span the whole tracked `work` library repo-wide
-- (fixing a false positive where cross-directory-but-real entities, e.g.
-- src/lib/hardware/debug/bscane2_tap_bridge.vhd, were misreported as
-- "undefined" because they lived outside the wrapper's own lane directory).
--
-- `totally_undefined_entity_xyz` is declared in NO tracked .vhd file
-- anywhere in this repository (verified via
-- `git grep -in "entity[[:space:]]\+totally_undefined_entity_xyz" -- '*.vhd'`
-- returning zero matches at the time this fixture was authored). If the
-- checker ever passes this fixture, its entity-definition resolution has
-- been over-broadened (e.g. degenerated into "assume defined unless every
-- possible source says otherwise") and rule 4 must be treated as broken.
--
-- Intended repo path (mirrors fake_step_counter_core.vhd's directory):
--   test/fixtures/riscv_truth/fake_wrapper_dangling_ref.vhd

entity fake_wrapper_dangling_ref is
  port (
    clk : in std_logic;
    rst : in std_logic
  );
end entity fake_wrapper_dangling_ref;

architecture rtl of fake_wrapper_dangling_ref is
begin
  u_ghost : entity work.totally_undefined_entity_xyz
    port map (
      clk => clk,
      rst => rst
    );
end architecture rtl;
