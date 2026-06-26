# Private `.spipe` overlay setup

Installers for an org that wants to use this public project privately: a private
`.spipe` overlay that holds an LLM wiki and a read-only copy of this project,
with no secret ever linked outside `.spipe/`.

## Layout produced

```
your-project/                 your repo
└── .spipe/                   your PRIVATE repo (submodule OR plain clone)
    ├── core/                 read-only copy of the public project (pull-only)
    ├── 00_llm_process/       LLM pipeline/process defs; reference 10_llm_wiki
    ├── 10_llm_wiki/          curated LLM wiki (public-safe, no secrets)
    └── 20_raw_doc/           raw source docs the wiki is distilled from
```

Read order is `00 -> 10 -> 20`. All git wiring stays inside `.spipe/`; the parent
repo at most references `.spipe` itself, never `core/` or upstream.

## Scripts

| Script | Run in | Does |
|--------|--------|------|
| `place_spipe.sh` / `.bat` | your project root | creates `.spipe` from your private repo, then calls `add_spipe_core` |
| `add_spipe_core.sh` / `.bat` | inside `.spipe` | vendors `core/` + creates the doc/wiki dirs |

```sh
# embed:    .spipe is a submodule of your project
# generate: .spipe is a plain clone, gitignored in your project (no outside link)
scripts/setup/spipe/place_spipe.sh [--vendor|--nested] <embed|generate> <private-spipe-repo-url> [core-url]
```

## gitignore is set at creation

- `generate` mode appends `/.spipe/` to your project's `.gitignore` automatically
  — the private overlay never enters your repo's history.
- No secrets are created or referenced; keep secret material under `.spipe/` only.

## `core/` is pull-only — two modes

`add_spipe_core [--vendor|--nested]` (forwarded by `place_spipe`):

| Mode | `core/` is | gitignored? | pull-only holds for | update |
|------|-----------|-------------|---------------------|--------|
| `--vendor` (default) | committed snapshot (`.git` stripped) | no — it travels in clones | **every clone** (no upstream link in the tree) | re-run the script |
| `--nested` | live clone (`origin` push disabled) | yes — `/core/` | only the machine that set it (config is per-clone) | `git -C core pull` |

Pick by whether `core/` should ride along when someone clones *your* `.spipe`:

- **`--vendor`** — copy travels, push-block is structural and guaranteed for
  all clones. Use when consumers should get `core/` automatically.
- **`--nested`** — lighter history, easy `git -C core pull`, but each consumer
  must reclone `core/` themselves and the push-block is local-only.

Neither grants write access to the public repo; the push-disable only stops
*accidental* pushes on a configured machine.
