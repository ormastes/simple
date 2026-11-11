# release/1.0.0 Windows sweep: caret + devhub unit lanes, fixes and one compiler blocker

2026-11-10, Windows 11 (Git Bash) interpreter lane, worktree based on
release/1.0.0 (2c4e59e). Full-directory runs of
`test/01_unit/app/devhub` (62 specs) and `test/01_unit/app/llm_caret`
(103 specs). This record lists every distinct defect found and its outcome.

## Fixed in this change

1. **JSON tokenizer index-space desync** — `json_skip_whitespace` walked
   bytes while its caller walked chars; any non-ASCII content corrupted all
   following tokens. See
   `json_skip_whitespace_byte_index_regression_2026-11-10.md`.
   (gh_json_roundtrip_spec)

2. **Reserved-word struct field** — `spawn` fields broke named-argument
   construction; renamed to `child_spawn` in `HostHelperStreamRetainedV1`
   and `ContainerOutputTurnV2`. See
   `simple_lang_reserved_word_struct_field_named_ctor_2026-11-10.md`.
   (8 caret specs + host_helper_settlement_v1 system spec)

3. **Unclosed `@when`** — `host_parent_budget_v1.spl` opened a second
   consecutive `@when(os="linux")` inside the first and never closed the
   block; merged the duplicated guard and added `@end`. (same 8 specs)

4. **Flat `else:` ladder in expression position** —
   `engine_exec_record_v3.spl:130-137` chained `else:` continuations at one
   indentation; the parser requires each else-body to nest. Rewrote as a
   `match` on the phase string. (same 8 specs)

5. **Assignment in one-line `else:`** — `else: self.authority[index] = entry`
   (simple_container_adapter_v2.spl:508) and the identical
   `smux_runtime_control_owner_v1.spl:156` are expression-only positions;
   expanded to block form. (cs_dashboard, cs_main, agent_workspace et al.)

6. **devhub fake-bin fixture visibility** — `test/fixtures/devhub/fake_bin.spl`
   declared its four helpers private while cmd_github/cmd_jira/cmd_tasks
   import them; made them `pub`. (3 devhub specs, 96 examples)

7. **wiki search row separators on Windows** — `_local_search` consumed
   `dir_walk` paths (OS-native `\`) against a `/`-normalized root, emitting
   `notes\page.md` ids `wiki_read` could not look up. Normalize the walked
   path before slicing. (infra_wiki_spec)

8. **mail timeout misclassified on Windows** — `_read_reply` distinguished
   timeout vs EOF by `now >= deadline`; Windows can surface the deadline as
   an empty read a quantum before the clock crosses it, reporting "mail
   server closed the connection before replying" for a silent server.
   100 ms tolerance band. (infra_mail_timeout_spec)

9. **smux reply guard smaller than the product's own requests** — the server
   replaced any reply over 64 KiB with `smux: reply exceeds limit`, while
   `capture_pane` routinely asks for `history-joined <session> 2000`; a pane
   holding one CLI run's compile-warning output (several hundred KiB)
   exceeds it. Raised `REPLY_LIMIT` to 1 MiB (both enforcement points share
   the const). (agent_workspace_spec own-pane exclusion example)

## Environment note: check-tree-size-push.shs storm (not this change)

Every `bin/simple test` invocation on this box spawns
`scripts/check/check-tree-size-push.shs`, and on this repo size those
checks do not terminate in any observable time: 100+ sh.exe walkers
accumulated between 2026-11-10 20:53 and 2026-11-11 morning, each holding
100-240 s of kernel time. The resulting disk contention makes the
process-spawning agent_workspace examples flaky in proportion to how many
walkers are live (its failures moved between unrelated examples across
runs with no code change). The hook needs a termination budget; that is a
CI-infra lane item, not fixed here.

## Fixed during the sweep (compiler-duplicate family)

- **main_spec / multimodal_proxy_spec, and the caret CLI itself**: the
  2026-11-09 nominal-owner resolution rejected co-compiled duplicate
  definitions that no import path selected:
  - `VirtMemManager` x3 (os/kernel/arch/x86_64/paging.spl,
    os/kernel/memory/vmm.spl, os/kernel/memory/vmm_core.spl): renamed the
    paging copy to `ArchPagingVirtMemManager` (the per-arch convention:
    `VirtMemManager32`, `Rv64VirtMemManager`) and the vmm_core copy to
    `VmmCoreVirtMemManager`. vmm.spl stays canonical (vmm_address_space
    imports it explicitly).
  - `mmio_read64`/`mmio_write64` x2 (boot/mmio facade vs
    boot/mmio_hardware raw owner), used bare by os/kernel/memory/vmm.spl:
    added the selective import `use os.kernel.boot.mmio.{mmio_read64,
    mmio_write64}` to vmm.spl.
  - `claude_cli.spl` `_json_i64` cast an optional with `as i64`
    (ERR-01): narrowed with `?? 0` first.
  Verification: `bin/simple.exe run src/app/llm_caret/main.spl workspace
  ... broadcast ...` now compiles and executes (previously died on the
  VirtMemManager ambiguity); both specs green.

## Still open (environment, not code)

- The worktree's `bin/simple.exe` is the Rust seed with a stale embedded
  stdlib; the JIT lowers main.spl against a `RingTelemetry` shape that no
  current source declares (`active_requests` field), demoting the whole
  module to the interpreter (~100-1000x slower startup). Per AGENTS.md the
  remediation is deploying the pure-Simple self-hosted binary, which is a
  bootstrap-lane decision, not this change.
