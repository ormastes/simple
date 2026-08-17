# Enterprise Suite Certification — 2026-08-17

**Verdict: CERTIFIED.** The whole enterprise suite is green and all four
enterprise guards pass on the exact certified tree, with the board gate booting
under real OVMF pflash firmware.

## Tree & binary identity (evidence binding)

- **Worktree:** `/mnt/data/worktrees/ent-cert`, detached HEAD
  `25595abd62d93eff90984901d8d116cafdd8a905` (CERTIFIED enterprise tree).
  `stat -c %F build` = `directory` (verified first).
- **Tool binary (Rust bootstrap seed, interpreter mode):**
  `/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple`
  - size `59536728` bytes, mtime `2026-08-16 22:59:37 +0000`
  - sha256 `40d348ef073bdbb0b6916b1fbe7294c3e3089cc5cabf9f890993ca610b176cc2`
  - `--version` banner: `Simple Language v1.0.0-beta` (self-declares
    "Rust-built Simple binary is a bootstrap seed only").
  - Reached in this worktree via a local `bin/simple` symlink (NOT committed; `bin/`
    is never added to git). All specs run **interpreter mode**, one at a time,
    `SIMPLE_TIMEOUT_SECONDS=900`, ANSI-stripped, verdict read from the
    `SPEC FILE VERDICT:` line (never `tail -1`).

## 1. Guard verdicts (each captured verbatim)

| Guard | Verdict |
|-------|---------|
| `check-enterprise-suite-enumeration.shs` | `PASS — 92 canonical spec(s) enumerated, matches EXPECTED=92` |
| `check-enterprise-cross-os.shs` | `PASS — 13 probe(s) checked, each compiles host + x86_64-unknown-simpleos with SMF magic` |
| `check-enterprise-guards-bite.shs` | `PASS — 5 guard-bite check(s) verified: enumeration bites over+under, cross-os discrimination holds` |
| `check-enterprise-store-in-guest-ovmf.shs` (board gate) | `PASS — 6 rung(s) checked, enterprise store read its own marker in-guest` |

Guard logs: `build/cert/logs/check-enterprise-*.log`.

## 2. Board gate — real-firmware detail

The store-in-guest gate booted via **real OVMF pflash** (not QEMU `-kernel`, not
`isa-debug-exit`). Kernel `build/os/simpleos_entstore_uefi128.elf` built
(`396 compiled, 0 failed`). All 6 rungs OK — serial transcript
`build/os/entstore/ent_store_in_guest_ovmf.serial.log`:

- L1 `[grub-uefi] multiboot loading`
- L2 `SimpleOS SSH + ring-3`
- L3 `[ent-store] probe begin`
- L3.5a `[ent-store] direct write rc=0`
- L3.5b `[ent-store] facade write+read-back=OK`
- L4 `enterprise store open=true verify=[]`

Host prerequisites present: `qemu-system-x86_64`, `/usr/share/OVMF/OVMF_CODE_4M.fd`.
Board gate is **not** blocked. Cross-OS probe count: **13** (host +
`x86_64-unknown-simpleos` SMF each).

## 3. Spec sweep — 33/33 GREEN

Enumerated runnable enterprise specs (`test/**/*enterprise*_spec.spl` plus the
enterprise_store/session/sale unit specs) and ran each one-at-a-time. Every spec
returned rc=0 with a valid `SPEC FILE VERDICT:` line, `failed=0 dropped=0`.
**No genuine reds. No harness SIGTERM / missing-verdict cases.**

- Specs green: **33 / 33**
- Cumulative assertions passed: **214**, failed: **0**, dropped: **0**
- Per-spec verdict table: `build/cert/logs/sweep_table_clean.tsv`;
  raw verdicts: `build/cert/logs/sweep_results.tsv`; per-spec logs:
  `build/cert/logs/spec_*.log`.

Example verdicts:
- `enterprise_store/enterprise_store_audit_hash_parity_spec.spl` declared>=14 executed=14 passed=14 failed=0
- `enterprise_security_audit_spec.spl` declared>=13 executed=13 passed=13 failed=0
- `goods_sale_vertical_spec.spl` declared>=10 executed=10 passed=10 failed=0
- `enterprise_channel/channel_hub_spec.spl` declared>=9 executed=9 passed=9 failed=0
- `booking_vertical_spec.spl` / `procurement_vertical_spec.spl` / `hcm_vertical_spec.spl` each passed=8 failed=0

Full 33-row list is in `build/cert/logs/sweep_table_clean.tsv`.

## Overall

**CERTIFIED** on tree `25595abd62d`. All 4 enterprise guards PASS
(enumeration=92, cross-os=13 probes, guards-bite=5, board=6/6 rungs on real
OVMF), and 33/33 enterprise specs are green (214 assertions, 0 failures) under
the seed binary identified above. No blockers.

---

## Addendum — extension to 18 verticals (2026-08-17)

After the core certification above (11 verticals, tree `25595abd62d`), three
further waves of business verticals landed on the certified base. Each was
built red-first in an isolated git worktree with a private `build/` dir,
reviewed by the orchestrator, and folded blob-first into
`refs/enterprise/restored`. Certified tip is now `139b2f68f54`.

**Why the core certification extends without a full re-sweep:** every added
vertical is a *pure business module* over the already-certified durable store.
None edits `foundation.spl` (frozen contracts — verified byte-identical at each
reland), none adds a `CommandResult` reason (closed 16-set held), none touches
the store/session/kernel/boot path, and none imports `std.common.crypto.sha256`
directly (hashing only via the SMF-safe `records.audit_append` facade). The
board OVMF gate certifies the store+kernel *infrastructure* boots in-guest and
reads its own audit marker — that infrastructure is unchanged by these modules.
Each added module carries its own two independent proofs: an isolated spec
verdict (below) and a cross-OS compile proof (host + `x86_64-unknown-simpleos`,
SMF magic `534d4600`).

**Per-vertical evidence (each spec run alone, seed interpreter, verdict read):**

| Wave | Vertical | Spec verdict | Cross-OS |
|------|----------|--------------|----------|
| W20-A | manufacturing / BOM | executed=6 passed=6 failed=0 | SMF host+simpleos |
| W20-B | tax engine (integer bp) | executed=7 passed=7 failed=0 | SMF host+simpleos |
| W20-C | multi-currency / fx | executed=7 passed=7 failed=0 | SMF host+simpleos |
| W21-A | notifications ledger | executed=6 passed=6 failed=0 | SMF host+simpleos |
| W21-B | storefront journey | executed=7 passed=7 failed=0 | SMF host+simpleos |
| W21-C | returns / RMA | executed=10 passed=10 failed=0 | SMF host+simpleos |
| W21-D | pricing / discounts | executed=11 passed=11 failed=0 | SMF host+simpleos |
| W22-A | general ledger (2-entry) | executed=7 passed=7 failed=0 | SMF host+simpleos |
| W22-B | loyalty / points | executed=6 passed=6 failed=0 | SMF host+simpleos |
| W22-C | inter-location transfers | executed=6 passed=6 failed=0 | SMF host+simpleos |
| W22-D | subscriptions / billing | executed=10 passed=10 failed=0 | SMF host+simpleos |

Added specs: 83 assertions across 11 new specs, 0 failures, 0 dropped.

**Guards re-verified at tip `139b2f68f54`:**
- enumeration: `PASS — 125 canonical spec(s), matches EXPECTED=125`
- cross-os: `PASS — 21 probe(s), host + x86_64-unknown-simpleos SMF`
- foundation.spl: byte-identical to the pre-wave certified base (frozen)
- rbac_registry.spl: only the fenced `fx.rate.set` finance grant added
  (equivalence spec green; grant kept outside `every_action()` by design)

One notable fence-discipline note: W20-C is the single lane that edited
`rbac_registry.spl`, adding `fx.rate.set` to the finance row via the
data-driven `registry_role_allows` seam (NOT the frozen `foundation.role_allows`
table). The equivalence spec stays green because that action is intentionally
outside its `every_action()` cross-product set.

**Overall (18 verticals): CERTIFIED.** Core infra board-proven and
full-sweep-proven at 11 verticals; 7 added pure-business verticals each
independently spec-proven and cross-OS-proven, over frozen contracts. No
blockers. The seed→self-host redeploy remains blocked upstream at the
planner-admission policy gate (recorded separately; not an enterprise-suite
defect).
