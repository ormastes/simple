# Committed `.spipe/policy/vcs.sdn` is rejected by its own canonical contract

**Status:** RESOLVED 2026-09-06
**Found:** 2026-09-05
**Severity:** blocks the `sj plan` PASS branch from binding to the canonical parser

## Symptom

```
$ bin/devhub lifecycle policy-check
{"output_version":"devhub/v1","status":"rejected","code":"POLICY_INVALID",
 "message":"review-ref policy does not match the canonical protected contract"}
exit 1
```

The repository's only committed protected-ref policy fails the repository's own
canonical validator. Read the exit status directly — this command emits a large
volume of `[gc-warning]`/`[use-warning]` lines first, and reading `$?` through a
pipe returns the pager's status, not the checker's.

## Two distinct defects, one already fixed

`.spipe/policy/vcs.sdn` has been tracked since `e274cd33719` (2026-08-27) and is
a genuine `spipe-vcs/3` document declaring all seven protected refs. Three
separate parser problems hid that fact:

1. **Schema clobber (FIXED 2026-09-05, `lifecycle_policy.spl:257`).**
   `parse_lifecycle_vcs_policy` was an indent-blind last-wins scan that bound
   *every* `schema:` line it saw. The nested `schema:` at `vcs.sdn:246`
   (`spipe-changed-path-manifest/1`) overwrote the header at `vcs.sdn:2`, so the
   document parsed as the wrong schema and was rejected with
   `unsupported or missing schema`.

2. **Section bleed (FIXED 2026-09-05, `lifecycle_policy.spl:276`).**
   With no block fence, `server_profiles:`'s own `update: deny` (`vcs.sdn:103`)
   overwrote the still-pending last ref entry, so a file that explicitly declares
   `append_only` for `recovery/*` was rejected with
   `recovery refs must be append-only`.

3. **Canonical contract divergence (OPEN — this record).**
   With both parser bugs fixed the basic parser accepts the file (`valid=true`,
   7 refs), but `parse_canonical_lifecycle_vcs_policy` still rejects it, because
   the committed policy and the canonical contract genuinely disagree:

   | ref | committed `vcs.sdn` | canonical contract demands |
   |---|---|---|
   | `review/*` | `force: deny` | `force: lease_only` |
   | `candidate/*` | profile `candidate` | profile `release` |

   These are policy disagreements, not parse errors. One of the two is wrong and
   a human needs to say which.

## Why it matters

`resolve_protected_target` (`src/app/sj/integrate_plan.spl:157`) is deliberately
bound to the BASIC parser, not the canonical one, precisely because binding to
canonical would leave the `sj plan` success branch dead — every plan would fail
on policy load rather than on its actual subject. That was the right call for
now, but it means **two parsers in the same lane currently disagree about the
same committed file**: `plan_integration_with_policy` (`:81`) is still
canonical-bound while `resolve_protected_target` is not.

That split must not become permanent. A policy engine with two validators that
disagree about the only policy in the tree is worse than one strict validator.

## Not yet established

- Which side is authoritative. The research docs
  (`doc/01_research/app/tools/scv/scv_jj_git_devhub_spipe_unified_lifecycle_full_2026-08-25.md`
  §7.1) give `review/<change-id>` as `lease/CAS allowed`, which reads closer to
  the canonical `lease_only` than to the committed `deny` — but §7.1 is research,
  not a ratified contract, and `vcs.sdn` was committed later.
- Whether `candidate/*` was intended to run the release gate profile or a
  lighter candidate profile. The research doc treats candidate refs as
  abandonable staging, which argues for the lighter profile the committed file
  already declares.

## Unblock

Decide the two rows above, then make the committed policy and the canonical
contract agree, then re-bind `resolve_protected_target` to the canonical parser
so the lane has exactly one validator. Until then, `policy-check` is honestly
RED and must not be wired into any gate tier.

## Evidence

No spec parses the committed file — every existing policy spec uses an inline
payload, which is why this survived. A regression spec that loads the real
`.spipe/policy/vcs.sdn` should land with the fix.

---

## Resolution (2026-09-06)

`bin/devhub lifecycle policy-check` now returns
`{"status":"ok","schema":"spipe-vcs/3","protected_ref_count":7}`, rc 0.

The user chose the **split fix**: each side was wrong about one row, so each side
changed once.

| row | change | why |
|---|---|---|
| `review/*` | `.spipe/policy/vcs.sdn` `force: deny` -> `lease_only` | research doc 1 section 7.1 gives review refs as "lease/CAS allowed"; the canonical contract was right |
| `candidate/*` | canonical expectation `release` -> `candidate` | candidate refs are abandonable staging, so the lighter profile the committed file already declared was right |

**A third defect surfaced underneath those two**, and it was not a policy
disagreement at all: `direct_protected_ref_update: deny` WAS present at
`vcs.sdn:61`, but `parse_lifecycle_vcs_policy` only read that key at indent 6
inside `ordinary_change:`, while the file declares it at indent 4 as a BLANKET
deny across every authoring mode. The parser was rejecting the policy for being
*stricter* than the form it knew. Fixed to accept both.

That is now the third indent-fragility bug in this one function (schema clobber,
section bleed, this). They are not three unrelated defects: it is a hand-rolled
line scanner doing a job that wants a real SDN parse. Treat a fourth as a signal
to replace the function rather than patch it again.

## Regression lock

The root cause of the whole episode was that **no spec ever read the committed
file** -- every policy spec used an inline payload, so the tree could diverge from
2026-08-27 to 2026-09-05 with everything green.
`test/01_unit/app/sj/protected_target_resolution_spec.spl` now parses
`.spipe/policy/vcs.sdn` by path through `parse_canonical_lifecycle_vcs_policy`
and asserts valid, schema, seven refs, and both repaired rows by name.

Proven to discriminate, not merely to pass: reverting `review/*` to `deny` takes
the file from `16 total, 16 passed` to `15 passed, 1 failed` with
`expected deny to equal lease_only`, and restoring returns it to 16/16 with the
policy file byte-identical.

## Still open, deliberately

`plan_integration_with_policy:81` remains canonical-bound while
`resolve_protected_target` uses the basic parser. Now that the committed policy
satisfies both, that split can be collapsed to one validator -- but that is a
behaviour change to the plan path and belongs in its own change, not this fix.

