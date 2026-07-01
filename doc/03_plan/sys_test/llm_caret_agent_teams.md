# LLM Caret Agent Teams - System Test Plan

Date: 2026-07-01

No system spec for the first slice. The supported behavior is request planning,
existing-file hash snapshots for caller-supplied paths, VCS changed-file
discovery, simple MCP/plugin manifest parsing, plugin install argv planning, and
small process-launch wrappers including non-persistent team launch, so unit
coverage plus source checks are the release gate. Add a system spec when
persisted team supervision, live MCP registry discovery, plugin install
execution, or live team interaction are selected.
