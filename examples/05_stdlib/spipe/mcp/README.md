# MCP

`server.js` is a dependency-free stdio JSON-RPC MCP server for SPipe docs and
experts.

Tools:

- `spipe_info`
- `spipe_experts`
- `spipe_read_doc`
- `spipe_fine_tune_guide`
- `spipe_fine_tune_model_guide`
- `spipe_fine_tune_template`
- `spipe_release_guide`
- `spipe_release_capabilities`

The release tools are read-only inspection surfaces. They report the packaged
policy and schema capabilities; they do not grant authority to update a
protected ref, sign a tag, or publish a release.

Resource:

- `spipe://skill`
