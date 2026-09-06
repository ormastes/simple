# rt_* API group policy + 2D/web optimization — agent research plan

**Created:** 2026-09-06
**Status:** in flight — 3 lanes landed or in review, 3 agent lanes running
**Goal (user's words):** "all rt_ access should through sosix or specific api
groups, not one by one. research rt and made policy and list up hal api groups
sosix, and other. make a sdn db about rt api group and api lists explained. ...
1. make rt api policy 2. not grouped rt api lint error. 3. register group api and
each rt api. 4. db like access to all other api also. do optimize simple 2d, web.
and rendering check and fix."

This plan exists because the four numbered items plus the two optimization items
were being worked as isolated incidents rather than as one program. It names the
lanes, what each owns, what is measured versus assumed, and what is NOT done.

## Measured starting state

| quantity | value | source |
|---|---|---|
| `rt_*` symbols registered | 4101 | `check-rt-api-groups.shs` on `work/rt-api-groups-enforce-2026-09-06` |
| unregistered symbols | 37 | same |
| groups over frozen call-site budget | 5 | same |
| API groups total | 43 unowned of ~180 | `rt_api_group_census_2026-09-06.md` |
| unowned groups with ZERO `src/**.spl` call sites | **22 of 43** | same census |
| direct forbidden `rt_` call sites under `src/` | **6322** vs ceiling 6240 | `check-no-direct-rt.shs --roots src` on pristine `origin/main` |
| Simple 2D vs C Vulkan | **C ~69x faster** (Simple 1.4% of C) | `doc/10_metrics/gpu/vulkan_2d_simple_vs_c_linux_2026-09-06.md` |
| web-render gates carrying a verdict | 92 of 97 (was 67) | `work/web-render-verdicts-finish-2026-09-06` |

**The R5 ceiling breach is new debt, not a moved goalpost.** `SRC_CEILING=6240`
is set once in `scripts/check/check-sosix-capsule-boundaries.shs:19` at commit
`4bd22ad051f` and `git log -S` confirms it has never changed. Since that commit,
+170/-37 `rt_` call lines landed under `src/**.spl`, **76 of them in
`src/lib/common/cache_host_authority_v1.spl` (56) and
`cache_daemon_host_authority_v1.spl` (20)** — the same `rt_cache_*` landing the
grouping gate flags as 37 unregistered symbols. It is currently RED on `main`, so
**every push needs `--no-verify`, which nullifies all 18 push gates.** Closing it
is the highest-leverage item in this plan and it is closed by landing lanes 3,
not by raising the ceiling.

## Lanes

### Lane 1 — policy + registry + advisory gate (item 1, item 3 partial)
`work/rt-api-groups-2026-09-06` (PR #405). Policy doc, `config/api/api_registry.sdn`,
`scripts/check/gen-api-registry.shs`, advisory gate, named-table support in
`src/lib/common/sdn/parser.spl`.
**Blocked on:** must not land without Lane 2 — on its own its floor is the
registry's own `sites` column, which its mandatory generator rewrites (`misc`
846→836), and `misc` counts as a group. Both are the things Lane 2 exists to fix.

### Lane 2 — ungrouped rt_ is a lint error (item 2)
`work/rt-api-groups-enforce-2026-09-06` (PR #419). `check-rt-api-groups.shs` +
frozen `rt_api_group_baseline.txt`.
**Two defects found on review, both open:** the manifest description claims
"green at tip" while the gate measures `FAIL — 37 unregistered, 5 over budget`;
and the title says ungrouped API is "a real error" while the manifest row is
`push_blocking=false`, i.e. advisory — it blocks nothing.
**Two suspected defects were tested and did NOT reproduce** — recorded so they
are not re-raised: `RT_API_GEN_BASELINE=1` in the env does not launder a PASS
(the mandatory fatal selftest fail-closes first; the baseline stays
byte-unchanged), and the stale-row limitation is disclosed in the verdict line
rather than hidden.

### Lane 3 — group ownership (item 3)
`work/rt-api-group-owners-2026-09-06` (PR #431). Closes `port` and `dma` by
routing 93 ad-hoc call sites through owners that already existed and had no
consumers. Drops forbidden 6322 → **6092**, i.e. 148 under the ceiling.
**The key structural finding:** a provider is derived from *allowlisted* calls,
so a group with no call sites is unownable by construction — that is 22 of the
43. Ownership cannot be the whole answer; policy must say what happens to a group
with no in-tree consumer.
**Deliberately left red:** `staged` meets the criterion but allowlisting it
*deletes* the group, because the generator's universe is C/Rust definition text
union the *forbidden* census and those symbols are in neither. Filed as
`doc/08_tracking/bug/rt_api_group_provider_erases_unbacked_group_2026-09-06.md`.

### Lane 4 — research, policy, and item 4 (RUNNING)
The layer above lanes 1-3, plus the item nobody has touched. Owns: the three-way
HAL / SOSIX / other classification the goal asks for; the decision of which
groups route through SOSIX versus a named owner; the disposition of the 22
zero-call-site groups; and **extending the SDN DB beyond `rt_*` to all public API
groups** ("db like access to all other api also"), proven on at least one
non-`rt_` family rather than stubbed across everything.

### Lane 5 — Simple 2D optimization (RUNNING)
Target is the 69x gap. Per Simple frame: draw 1.9 ms, submit_batch 2.2 ms,
present 2.8 ms, readback 0.4 ms ≈ 7.3 ms, against C's 0.108 ms for the whole
frame. **The even spread across draw/submit/present is the signature of per-op
marshalling across the Simple↔runtime boundary, not GPU time.**
Ruled out by measurement, so not to be re-litigated: it is not the software
rasterizer (both legs land on `NVIDIA GB10`; `llvmpipe` is GPU1 and unused), not
the interpreter (no `[jit-fallback]` for the bench module), and not a missing
Vulkan extension (`VK_KHR_surface` rev 25 present).

### Lane 6 — web rendering check and fix (RUNNING)
A sibling lane made the web-render gates honest but fixed no rendering, and was
candid that PASS tails were exercised on only 3 of them — the rest are
unexercisable on this host. Lane 6 must first settle whether a renderable path
exists here at all (`VK_EXT_headless_surface` IS available) or whether
`simple-bin-forbidden` is structurally unsatisfiable on an aarch64 host with zero
tracked aarch64 binaries — then fix actual rendering defects on whatever path is
runnable.

## Standing rules for every lane

These are here because each has already produced a false result in this program.

- **Verdict convention is mandatory.** Last stdout line is `PASS — <n> ...
  checked` with n>0, `FAIL — ...`, or `ERROR — nothing was checked`. Zero checked
  is ERROR, never PASS.
- **Never read an exit status through a pipe.** `cmd | tee` and `cmd | grep`
  return the last command's status. This produced a fail-open compare gate
  (`compare_status=fail`, exit 0) and a `bench_rc` that was assigned but never
  tested, so a dead bench printed *zero bytes* with no verdict.
- **Never add a PASS tail to a path you cannot exercise.** A gate claiming PASS
  on an unexercisable path is worse than a silent one.
- **Never regenerate a baseline or raise a ceiling to clear a red.** A red gate
  stops ratcheting, which is how the port-I/O adapter contract decayed to one
  consumer unnoticed.
- **Pin a worktree to a sha before measuring.** The stdlib is read as SOURCE on
  every run and parallel sessions edit `src/lib/**` continuously; an A/B against
  the shared clone measures the other session. This already produced a
  decisive-looking, worthless result in this program.
- **Separate MEASURED from INFERRED when reporting.** Several claims in this
  program have been falsified on re-check, in both directions — including two
  independent reviewers reporting the same two false HIGH findings.

## Not done, and not owned by any lane

- Promoting the rt_ group gate from advisory to blocking. Four blockers: `rg`
  dependence, the 22 unownable groups, the gate FAILing on `main`'s drift
  regardless of ownership, and the group-erasure bug.
- Deciding restore-vs-retire for the x86 port-I/O adapter contract
  (`doc/08_tracking/bug/x86_port_io_adapter_contract_decayed_spec_red_on_main_2026-09-06.md`).
  That is the OS lane owner's call.
- The JIT arena follow-ups: no `munmap` anywhere, and the vendored patch has no
  guard so `cargo vendor` silently reverts it — in a directory CLAUDE.md line 55
  tells every scan to skip.
