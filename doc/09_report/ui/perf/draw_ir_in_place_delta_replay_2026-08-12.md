# DrawIR in-place delta replay evidence — 2026-08-12

Status: **CORRECTNESS PASS / FULL-COPY REMOVED / 8K80 NOT PROVEN**

Canonical `draw_ir_delta_replay` previously copied the complete prior command
array before patching changed entries. That makes a one-component retained
frame O(total commands) in copied command material even when delta generation
is damage-proportional.

The additive `draw_ir_delta_replay_into` API patches caller-owned retained
storage directly and returns the exact number of valid entries applied.
Mismatched arrays and invalid indices fail closed. The existing copying API is
preserved and delegates to the same patch loop, retaining its value semantics.

Focused coverage passed: one dirty component applied exactly one write, all
three untouched commands remained field-identical, and the resulting retained
array matched a fresh full rebuild. Existing empty-delta, stale-geometry,
proportionality, and copying-replay sabotage coverage remained green.

O3 analysis completed with 18 further opportunities. Production compositor
and advanced DrawIR executor files were concurrently modified and were not
edited; they can adopt the additive API when ownership clears. This is not an
end-to-end 7680x4320 timing row and makes no 8K/80 claim.
