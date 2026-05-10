# W-5 Done Note — Field-Index-Assign Audit (wave 3)

Date: 2026-04-25.
Scope: caller-side `obj.field[i] = x` / `g_state.field[i] = x` audit
across the security-relevant subtree.

## Outcome

- **Total code-level hits in W-5 scope: 0.**
- **(B) fixes applied by W-5: 0.**
- **(R) ambiguous: 0.**
- **(B) hits in user WC `sshd/`: 0** (subtree clean of pattern).
- The single raw grep hit (`random.spl:249`) was a **docstring quote** of
  the bug pattern, not real code. The actual code in `random.spl` already
  uses constructor-rebind (W-1's WC change, not in W-5 turf).

## Deliverables

- Audit report:
  `.sstack/crypto-pure-simple-port/research/w5_field_index_assign_audit.md`
- This done note:
  `.sstack/crypto-pure-simple-port/impl/w5_audit_done.md`
- **No source files modified.**
- **No regression spec added** — no (B) hit available to exercise.

## Blocker / Caveat for orchestrator

The brief's hard-required reading
(`bug_interpreter_struct_field_index_assign_2026-04-25.md`,
`bug_csprng_rekey_silent_noop_2026-04-26.md`, and the constructor-rebind
exemplar `src/lib/common/math/bignum/fixed.spl:404`) is **not present in
this branch**. The bignum subtree is missing entirely from
`src/lib/common/`. Wave-2 work has not been merged into this branch's
`HEAD`. The audit therefore could not consult the 7-row "Confirmed
scope" table; classification by intuition aligned with the documented
pattern's plain reading.

Recommended orchestrator action: rebase wave-2 docs + bignum source onto
this branch (or note that wave-3 audits should run from a
wave-2-inclusive base).

## advisor() interactions

1. **Mid-audit:** flagged that bug docs and exemplar are missing from the
   tree; recommended supplementary regex variants (multi-line value,
   chained receiver) and explicit documentation of the gap. **Handled:**
   ran both extra variants (zero additional hits), surfaced the gap in
   the audit report.
2. **Pre-done:** (this is the report-and-stop call following the advisor
   protocol).

## Acceptance check

- Audit table accurate: yes.
- (B) hits in scope all fixed: yes (vacuously — zero hits).
- Deliberate-fail proof on at least one: **moot** (no (B) target).
- No regressions in existing direct-invocation specs: yes
  (no source modifications were made by W-5).
