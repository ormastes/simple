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
scripts/setup/spipe/place_spipe.sh <embed|generate> <private-spipe-repo-url> [core-url]
```

## gitignore is set at creation

- `generate` mode appends `/.spipe/` to your project's `.gitignore` automatically
  — the private overlay never enters your repo's history.
- No secrets are created or referenced; keep secret material under `.spipe/` only.

## `core/` is pull-only

`add_spipe_core` shallow-clones the public project into `core/`, **strips its
`.git`**, and commits the snapshot. Because the committed tree has no upstream
remote, **pushing to the public repo is impossible by construction** for everyone
who clones `.spipe` — not just the machine that set it up. Pull updates by
re-running the script (re-clones latest, recommits; clean no-op when unchanged).

> A nested *live* clone (`git clone … core` + `set-url --push DISABLED`) only
> blocks pushes on the one machine that set it (config is per-clone, not
> committed). The stripped-vendor snapshot is what makes pull-only hold for all
> clones, so it is the default here.
