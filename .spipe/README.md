# Simple SPipe Host Mount

This directory is the host-local SPipe mount for the Simple repository.

- `.spipe/spipe` is the compatibility submodule mount for reusable SPipe assets.
- `.spipe/spipe_project` links to `examples/spipe`, the standalone SPipe example
  project submodule.
- `.spipe/doc` links to this host project's configured LLM process docs:
  `doc/00_llm_process`.
- `.spipe/domain_expert`, `.spipe/template`, `.spipe/spipe_docs`,
  `.spipe/project_expert/spipe`, and `.spipe/tool_expert/spipe_submodule` link
  to common process and expert roots inside the standalone SPipe project.

The upstream SPipe project is `https://github.com/ormastes/Spipe.git`.

The generic SPipe default process-doc root is `doc/llm_process`. This host
overrides it in `.spipe/config.sdn` with `host_process_doc: doc/00_llm_process`.
Run `node .spipe/spipe_project/cli/spipe.js doc-link .` to recreate the
`.spipe/doc` link from that configuration.

Run `sh scripts/setup-spipe-submodule.shs` to initialize both SPipe submodules,
refresh `.spipe/spipe_project`, `.spipe/doc`, and the top-level common process
links, then recreate the configured doc-root process links.

Run `sh scripts/check-spipe-submodule-gitlinks.shs --check` to verify that
`.spipe/spipe` and `examples/spipe` are parent gitlinks. Use `--repair` if a
recursive `git add examples/spipe` accidentally cached submodule files.
On Windows, use
`powershell -ExecutionPolicy Bypass -File scripts\check-spipe-submodule-gitlinks.ps1 --check`
or `--repair`.

Run `node .spipe/spipe_project/cli/spipe.js doctor .` to verify the host mount
links and reusable process surfaces.

Host-specific SPipe state remains in sibling `.spipe/<feature>/` directories.
Reusable domain, SPipe, template, and tool expert roots are linked into
`doc/00_llm_process/` by the SPipe setup script.
