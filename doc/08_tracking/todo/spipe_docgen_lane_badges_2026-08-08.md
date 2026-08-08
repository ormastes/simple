# SPipe-Docgen Per-Cell Lane Badges

Rendering of lane badges in notebook spec manuals when lane-gated specs land.

# TODO: [spipe_docgen][P2] Render per-cell `%%mode` lane badges in notebook spec manuals
When notebook specs with per-cell lane gating (`%%mode` directives) are integrated, `src/app/spipe_docgen/` should generate scenario manuals that render lane-mode badges for each cell (visual indication of which lane/mode the cell runs under). This keeps the manual documentation in sync with the actual cell behavior. See design: `doc/05_design/app/tools/notebook_lanes_architecture.md` § Docgen and `doc/00_llm_process/feature_expert/notebook_lanes/skill.md`. Note: output generated to `doc/06_spec/` via `--generate` flag; do NOT hand-edit generated manuals.
