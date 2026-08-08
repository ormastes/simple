# Perf Checklists TL;DR (AC-2) — full: `perf_checklists.md` — 58 items, 6 domains

## 6-Domain Status (`[x]`=done `[~]`=partial `[ ]`=open)

| Domain | Baseline? | Opt landed? | Re-measured? |
|---|---|---|---|
| language-script (interp) | [ ] | [x] micro-opts; [ ] MIR 2-8 OPEN | [ ] |
| language-compiler (smf+native) | [ ] | [~] AC-7 dynSMF spawn+hash+spec PARTIAL | [ ] |
| web server | [ ] | [x] H2/H3/QUIC/static/net-accel | [ ] |
| db-RAM | [ ] | [~] index phases 6-8 open | [ ] |
| db-persistent | [ ] | [~] WAL blank-row P0 bug open | [ ] |
| os (x86_64) | [ ] | [x] fs/scheduler; [ ] Cranelift inlining | [ ] |

All baselines OPEN. rt_* baseline: nogc_sync_mut 7,974 + nogc_async_mut 2,249 lines (no sweep).

## Harness → Domain Mapping

```sdn
flow {
  cross_lang_perf_shs -> { lang_script_section, lang_compiler_section }
  smf_cache_reuse_spec -> lang_compiler_section
  web_server_bench_spec -> web_section
  db_ram_vs_persistent_bench_spec -> { db_ram_section, db_persistent_section }
  os_fs_sched_bench_spec + qemu_os_harness -> os_section
  check_api_arch_guard_shs -> all_sections[api_guard_row]
  symbol_analyzer_spl + metadata_symbol_surface_spl -> check_api_arch_guard_shs
}
```
