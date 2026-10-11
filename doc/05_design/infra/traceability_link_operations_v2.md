# Targeted authored link operations, declarations major2

Status: design AstraPASS P0=0/P1=0; final component source/oracle/evidence AstraPASS P0=0/P1=0. Authority: full report sections7.3–7.5,8.2,20;
all20REQ/40AC/WP0–WP7 remain required. This addresses an explicit major1 gap,
not a narrower replacement scope. No runtime or authenticated admission claim.

Major1 remains byte-compatible data with its original signatures. Major2 retains
the same four collection tables and flat envelope id/namespace, adding required
explicit_links and replacement_scopes tables, including when empty. A new typed
TraceDeclarationsV2 contains base:TraceDeclarationsV1 plus both collections.
The generic document enum gains a separate DeclarationsV2 variant; only this
family accepts major2. There is no automatic migration, inferred review or
reinterpretation of major1 records as override authority.

| table | exact columns |
|---|---|
| explicit_links | id, owner, from_id, relation, to_id, operation, replaces_rule, reason, origin_id, exception_id |
| replacement_scopes | operation_id, from_id, relation, to_id |

Explicit link id/owner/endpoints are restricted identities; relation uses the
existing14 claim relations. Reason is nonempty UTF8; origin_id closes to the
base origins table. Operation enum is add/replace/suppress. IDs are unique within
their typed table; operation_id is the unique key of replacement_scopes.
Every scope operation_id resolves to an existing replace operation; orphan scopes
reject. Scope endpoints and relation use the same ID/relation validators as links.

Add contributes a desired relation. replaces_rule and exception_id must be empty,
and no replacement scope may refer to it. Ordinary intrinsic claims need no
redundant add row. Replace contributes its desired from/relation/to tuple but
requires a named rule, a referenced applicability exception and exactly one
replacement_scopes row describing the original from/relation/to tuple. Suppress
uses its own tuple as the exact original relation to suppress and requires a
named rule and applicability exception; no redundant replacement_scope is allowed.
An applicability exception must exist and name the same rule. Its owner, reason,
review-state and expiry are retained data, not authenticated permission.

All endpoints and rules remain external references for the resolver. A codec
cannot prove the original edge exists, rule still matches, scope is authorized,
exception currently applies or the desired relation is eligible. The WP2 resolver
must diagnose those failures, including stale replacement. Preserve conflicting
and overlapping operations for resolution; never pick a first operation, merge
scopes, apply a global suppression, infer policy authority or grant verification.

## Budgets and shared owners

Reuse major1 limits and base carrier validation. Major2 has fixed63 nodes plus
all primitive cells, depth3 and max10 columns. Total rows include all six tables;
cells=5C+4A+10E+7O+10L+4S. Count, text/UTF8/field and exact escaped output preflight
precede producer reference indexes, SDN rows and sort keys. Exact size adds the
two headers and their canonical rows to the existing major1 size; a one-digit
schema version change preserves prefix length. Sort complete records with the
parent byte-order owner and render through the shared SDN writer.

The public major2 from-value adapter independently validates raw semantic counts
and cumulative key/header/string bytes before exact field diagnostics. One
strict source parse precedes typed adaptation; do not serialize/reparse the
base. After total raw row preflight, create a fixed seven-key major1 view with an
explicit version1 schema and invoke the existing bounded base adapter. This is
an internal view, not an importer, admitted record or source identity. Validate
the new tables and complete major2 contract before returning the typed document.

Encoding first validates whole major2 preflight, then base and operation reference
semantics. The existing bounded major1 encoder may be reused after this gate,
with its constant additional O(base records/text) validation documented here;
avoid per-row revalidation, quadratic table concatenation or repeated source scans.
Only the fixed schema prefix changes to major2; append the two canonical tables.
CPU/RSS/coverage remain unqualified until the full selected NFR checks.

## TDD and review

Run strict-valid major2 through the unchanged document dispatcher: acceptance
must actually fail with schema_version. Assert precise duplicate-operation and
missing original-scope outcomes, not arbitrary Err. Then add typed payload,
add/replace/suppress shape, referenced rule/exception closure, conflict retention,
canonical permutations, exact63+cells budgets, raw bounds and schema separation
cases using step helpers and real built-in matchers. These are AC001/002
component contributions; real targeted/stale resolution AC006 remains required.
Astra reviews design and final source/oracles/logs. Renew affected generic major1
acceptance and summary dispatcher tests only after relevant source changes.

## Observed component stage

Native strict-valid baseline3/3 -> initial typed3/0 precedes broader12/0 and
spec-only coverage renewal14/0. Affected major1 declarations13/0 and summary15/0
are renewed after generic dispatcher changes. The final spec checks empty63-node
shape, exact combined text budgets and payload reference IDs. Source/oracle
AstraPASS P0=0/P1=0; final evidence hash review PASS (10source/36artifacts reconciled). Full scope remains open.
