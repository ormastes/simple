# doc/05_design/nvfs/

NVMe-aware filesystem design notes. **Two parallel tracks publish here:**

- **nvfs track** (filesystem agent) — writes the canonical design at `nvfs_design.md` (to be created) and responds to client requirements.
- **svllm track** (serving-engine agent) — publishes `svllm_requirements.md` upfront so filesystem decisions are grounded in a real client.

## Files in this directory

| File | Owner | Purpose |
|---|---|---|
| `svllm_requirements.md` | svllm track | Upfront fs API / semantics svllm needs; updated per svllm sub-phase |
| `nvfs_design.md` | nvfs track | (to be created) canonical filesystem design |
| any other `*_requirements.md` | other client tracks (DB, future) | Per-client requirement contributions |

## Coordination protocol

- Client tracks (svllm, db-engine, etc.) each own one `<client>_requirements.md` file here.
- The nvfs track reads all `*_requirements.md` as design input.
- When nvfs's design forces a client to adapt, the nvfs agent opens a section in `nvfs_design.md` naming the impacted client; that client updates its own requirements file.
- Reactive feature-requests that arise mid-implementation go under `../svllm/fs_requests/` (or `../<client>/fs_requests/`) and are promoted here only if they change the design.

## Research reference

The attached research doc supplied by the user (pasted into the original `/dev` request) is the shared starting point for both tracks. A trimmed copy for svllm lives at `../svllm/svllm_master_plan.md`; the nvfs track may mirror or reference it as needed.
