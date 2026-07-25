# svllm → nvfs Feature Request Log

**Secondary channel** for filesystem feature requests that surface during svllm implementation. The **primary** channel is the upfront design-doc contribution at `../../nvfs/svllm_requirements.md`. Use this directory only when:

- An implementation step hit a limitation not anticipated in the requirements doc, **and**
- The limitation is reproducible and has a measured cost, **and**
- It does not fit cleanly as an edit to the requirements doc (yet).

If the discovery changes the design rather than just reporting a perf gap, promote it into `svllm_requirements.md` and delete/supersede the entry here.

## Filing a request

One markdown file per request, filename `YYYY-MM-DD_<short-slug>.md`.

### Template

```markdown
# FS-REQ-<nnn>: <one-line title>

- **Date:** YYYY-MM-DD
- **svllm phase:** A<n>
- **Triggering code:** `<path>:<line>`
- **Need (API or semantic):** <one sentence>
- **Current workaround:** <what we do today; perf/complexity cost>
- **Measured impact:** <e.g., "tensor-pack load is 3.2× slower than raw bandwidth because the handle caps at 8 concurrent reads">
- **Proposed mapping:** `fs_<verb>(<args>)` per `../../nvfs/svllm_requirements.md` §R<n>
- **Priority:** P0 (blocks phase exit) / P1 (degrades perf target) / P2 (nice-to-have)
- **Status:** open / accepted-into-nvfs / declined / superseded
```

### Registration

After filing, cross-register in the repo's bug/feature tracker so it surfaces in auto-generated status:

```bash
bin/simple bug-add --id=FS-<nnn> --title="<same title>" --path=doc/05_design/svllm/fs_requests/<file>
```

If a dedicated FEAT tracker is added later (see approved plan Phase A0 micro-task), switch to that.

### Promotion to upfront design doc

When a request is accepted into the nvfs design:

1. Edit `../../nvfs/svllm_requirements.md` to reflect the new or updated requirement.
2. Set this request's `Status:` to `accepted-into-nvfs`.
3. Reference the commit/section that promoted it.

## Files in this directory

- `README.md` (this file)
- `FS-REQ-*.md` — individual requests, newest first when listed

(Empty on first PR; populated as svllm implementation progresses.)
