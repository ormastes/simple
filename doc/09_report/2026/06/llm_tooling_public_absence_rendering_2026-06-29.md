# LLM Tooling Public Absence Rendering Evidence

- status: `pass`
- reason: `absence_markers_absent`
- required_gates: `nil_marker_absent,option_none_absent,empty_string_absent`
- blocked_gates: `none`
- surface_manifest: `build/llm_tooling_public_absence_rendering/public_absence_surface_manifest.tsv`
- surface_manifest_count: `121`
- surface_manifest_size: `16461`
- surface_manifest_sha256: `eb48b3b3410780988a0be905e0478a70ac9fecfe456b05cc2aa6e827a70bf35c`
- failure_count: `0`
- next_action: `rerun after public manual or dashboard wording changes`

The guard scans public manuals, generated/manual SPipe docs, dashboard wording, LLM runtime evidence reports, and strict blocker tracking surfaces that expose absence states. It excludes fenced code and executable SSpec details in Markdown so internal Simple source examples can still document implementation syntax.
