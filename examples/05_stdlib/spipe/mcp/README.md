# MCP

`server.js` is a dependency-free stdio JSON-RPC MCP server for SPipe docs,
experts, release planning, and compiled knowledge queries.

Tools:

- `spipe_info`
- `spipe_experts`
- `spipe_read_doc`
- `spipe_fine_tune_guide`
- `spipe_fine_tune_model_guide`
- `spipe_fine_tune_template`
- `spipe_release_*_plan`
- `spipe_folder_reverse_references`

`spipe_folder_reverse_references` accepts an immutable compiled-inventory JSON
path, a target UID, an optional canonical project-relative `folder_path`, and
explicit `limit`/`max_work_units` bounds. Results are ordered by canonical
source path and edge identity. Continue with the returned authenticated
`next_cursor` using exactly the same query arguments. The server caches at most
eight compiled indexes and invalidates one when file identity, size, mtime, or ctime
changes. Each request opens once with no-follow semantics, fingerprints with
`fstat`, and reads/rechecks that same descriptor, so pathname replacement
cannot redirect an in-flight query. It never scans the workspace in a request
handler.

Resource:

- `spipe://skill`
