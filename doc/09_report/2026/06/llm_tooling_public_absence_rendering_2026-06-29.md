# LLM Tooling Public Absence Rendering Evidence

- status: `pass`
- reason: `absence_markers_absent`
- required_gates: `nil_marker_absent,option_none_absent,empty_string_absent`
- blocked_gates: `none`
- surface_manifest: `build/llm_tooling_public_absence_rendering/public_absence_surface_manifest.tsv`
- surface_manifest_count: `93`
- surface_manifest_size: `12660`
- surface_manifest_sha256: `564c57ce69260d0dbd96a5f6995f123de0a3b14024831464ec60cfbd2551282f`
- failure_count: `0`
- next_action: `rerun after public manual or dashboard wording changes`

The guard scans public manuals, generated/manual SPipe docs, dashboard wording, and LLM runtime evidence surfaces that expose absence states. It excludes fenced code and executable SSpec details in Markdown so internal Simple source examples can still document implementation syntax.
