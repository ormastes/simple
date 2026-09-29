# Enterprise Suite — Attribute-context XSS, END-TO-END through the real dispatcher

> Escaping was proven end-to-end only for ELEMENT context: the adversarial

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Enterprise Suite — Attribute-context XSS, END-TO-END through the real dispatcher

Escaping was proven end-to-end only for ELEMENT context: the adversarial

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/simple_erp.md |
| Design | N/A |
| Research | doc/01_research/app/enterprise/simple_enterprise_suite_assessment_and_parallel_plan_2026-08-16.md |
| Source | `test/03_system/app/enterprise/enterprise_attribute_escaping_e2e_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Why this spec exists (the gap it closes)

Escaping was proven end-to-end only for ELEMENT context: the adversarial
audit (`enterprise_security_audit_spec`) drives `<script>alert('x')</script>`
through the real dispatcher and asserts the body carries `&lt;script&gt;`, not
a live `<script>`. But `<script>` contains no `"` — it can never prove the
ATTRIBUTE-context breakout, where an attacker closes a double-quoted attribute
early (`x" onmouseover="alert(1)`) or breaks out of the tag entirely
(`x"><img src=y onerror=z>`). That breakout was only ever proven at the `esc()`
PRIMITIVE level (`enterprise_output_escaping_audit_spec` calls `esc()` directly,
zero dispatches) — nothing drove such a payload THROUGH A REAL ROUTE that
renders it into an HTML attribute and asserted the rendered attribute is safe.

This spec does exactly that. Every `<... data-*="...">` attribute site in the
app renders attacker-influenceable data:

- `/store/catalog`     — `data-sku="…"`      (product sku)
- `/hcm/employees`     — `data-employee="…"` (employee id)
- `/proc/pos`          — `data-po="…"`       (purchase-order id)
- `/booking/resources` — `data-resource="…"` (resource id)

For each, we seed a record whose id carries an attribute-breakout payload,
drive the REAL `store_app_handle`, and assert the rendered body contains the
payload ONLY in escaped form (`&quot;`, `&lt;img`) and NEVER the live breakout
(`" onmouseover=`, `<img`).

## Bite proof (recorded in the W17-A state entry)

Neutering the quote-escape in `web_common.esc()` (dropping the
`replace("\"", "&quot;")` line) turns every `LIVE_QUOTE_BREAKOUT` assertion
below RED — the raw `" onmouseover=` reaches the body. Restoring it returns
the spec to GREEN. That is the proof these assertions BITE on the attribute
axis specifically, which the element-context `<script>` audit cannot.

## Troubleshooting

- A live `" onmouseover=` or `<img` in a body means a view interpolated an id
  into a double-quoted attribute WITHOUT `esc()` (or `esc()` stopped escaping
  `"`/`<`) — fix the view / the primitive, NEVER the expectation.

**Requirements:** N/A
**Plan:** doc/03_plan/agent_tasks/simple_erp.md
**Design:** N/A
**Research:** doc/01_research/app/enterprise/simple_enterprise_suite_assessment_and_parallel_plan_2026-08-16.md

Lane: .spipe/simple_enterprise_suite (v2, W17-A).

## Scenarios

### attribute-context XSS renders escaped through every data-* route

#### escapes an attribute breakout in the CATALOG data-sku attribute

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- escapes an attribute breakout in the CATALOG data-sku attribute
   - Expected: http_status_code(cat.status) equals `200`
   - Expected: "catalog-has-attr=" + "{cat_has_attr}" equals `catalog-has-attr=true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("escapes an attribute breakout in the CATALOG data-sku attribute")
val store = fresh("catalog")
val t = tenant()
val a = admin()
val sa = admin_session()
sale_add_product(store, sa, t, a, quote_breakout(), "Widget", Money(amount_cents: 100, currency: "USD"))
sale_add_product(store, sa, t, a, tag_breakout(), "Gadget", Money(amount_cents: 200, currency: "USD"))

val cat = store_app_handle(store, sa, t, a, "GET", "/store/catalog", plain_headers(), "")
expect(http_status_code(cat.status)).to_equal(200)
val cat_has_attr = cat.body.contains("data-sku=")
expect("catalog-has-attr=" + "{cat_has_attr}").to_equal("catalog-has-attr=true")
assert_attr_safe("catalog", cat.body)
store_close(store)
```

</details>

#### escapes an attribute breakout in the HCM data-employee attribute

- escapes an attribute breakout in the HCM data-employee attribute
   - Expected: http_status_code(emp.status) equals `200`
   - Expected: "hcm-has-attr=" + "{emp_has_attr}" equals `hcm-has-attr=true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("escapes an attribute breakout in the HCM data-employee attribute")
val store = fresh("hcm")
val t = tenant()
val a = admin()
val sa = admin_session()
hcm_hire(store, sa, t, a, envelope("k-h1", "hcm.hire"), quote_breakout(), "Alice", 100, 1000, 40)
hcm_hire(store, sa, t, a, envelope("k-h2", "hcm.hire"), tag_breakout(), "Bob", 100, 1000, 40)

val emp = store_app_handle(store, sa, t, a, "GET", "/hcm/employees", plain_headers(), "")
expect(http_status_code(emp.status)).to_equal(200)
val emp_has_attr = emp.body.contains("data-employee=")
expect("hcm-has-attr=" + "{emp_has_attr}").to_equal("hcm-has-attr=true")
assert_attr_safe("hcm", emp.body)
store_close(store)
```

</details>

#### escapes an attribute breakout in the PROC data-po attribute

- escapes an attribute breakout in the PROC data-po attribute
   - Expected: http_status_code(pos.status) equals `200`
   - Expected: "proc-has-attr=" + "{pos_has_attr}" equals `proc-has-attr=true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("escapes an attribute breakout in the PROC data-po attribute")
val store = fresh("proc")
val t = tenant()
val a = admin()
val sa = admin_session()
proc_supplier_add(store, sa, t, a, "SUP-1", "Supplier One")
proc_requisition_create(store, sa, t, a, envelope("k-req", "proc.requisition.create"), "REQ-1", "SKU-1", 5)
proc_requisition_approve(store, sa, t, a, envelope("k-appr", "proc.requisition.approve"), "REQ-1")
proc_po_create(store, sa, t, a, envelope("k-po1", "proc.po.create"), quote_breakout(), "REQ-1", "SUP-1", Money(amount_cents: 400, currency: "USD"))
proc_requisition_create(store, sa, t, a, envelope("k-req2", "proc.requisition.create"), "REQ-2", "SKU-1", 5)
proc_requisition_approve(store, sa, t, a, envelope("k-appr2", "proc.requisition.approve"), "REQ-2")
proc_po_create(store, sa, t, a, envelope("k-po2", "proc.po.create"), tag_breakout(), "REQ-2", "SUP-1", Money(amount_cents: 400, currency: "USD"))

val pos = store_app_handle(store, sa, t, a, "GET", "/proc/pos", plain_headers(), "")
expect(http_status_code(pos.status)).to_equal(200)
val pos_has_attr = pos.body.contains("data-po=")
expect("proc-has-attr=" + "{pos_has_attr}").to_equal("proc-has-attr=true")
assert_attr_safe("proc", pos.body)
store_close(store)
```

</details>

#### escapes an attribute breakout in the BOOKING data-resource attribute

- escapes an attribute breakout in the BOOKING data-resource attribute
   - Expected: booking_create_resource(store, sa, t, a, quote_breakout(), "capacity-pool", 2, "v1").reason equals `accepted`
   - Expected: booking_create_resource(store, sa, t, a, tag_breakout(), "capacity-pool", 2, "v1").reason equals `accepted`
   - Expected: http_status_code(res.status) equals `200`
   - Expected: "booking-has-attr=" + "{res_has_attr}" equals `booking-has-attr=true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("escapes an attribute breakout in the BOOKING data-resource attribute")
val store = fresh("booking")
val t = tenant()
val a = admin()
val sa = admin_session()
expect(booking_create_resource(store, sa, t, a, quote_breakout(), "capacity-pool", 2, "v1").reason).to_equal("accepted")
expect(booking_create_resource(store, sa, t, a, tag_breakout(), "capacity-pool", 2, "v1").reason).to_equal("accepted")

val res = store_app_handle(store, sa, t, a, "GET", "/booking/resources", plain_headers(), "")
expect(http_status_code(res.status)).to_equal(200)
val res_has_attr = res.body.contains("data-resource=")
expect("booking-has-attr=" + "{res_has_attr}").to_equal("booking-has-attr=true")
assert_attr_safe("booking", res.body)
store_close(store)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/agent_tasks/simple_erp.md`
- **Research:** `doc/01_research/app/enterprise/simple_enterprise_suite_assessment_and_parallel_plan_2026-08-16.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `cdb651c174be073e39ac61d35ddc27b90fce15456c4a6e4be9b998ffcdf098ef`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `cdb651c174be073e39ac61d35ddc27b90fce15456c4a6e4be9b998ffcdf098ef`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `cdb651c174be073e39ac61d35ddc27b90fce15456c4a6e4be9b998ffcdf098ef`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/app/enterprise/enterprise_attribute_escaping_e2e_spec.spl
mirror: doc/06_spec/03_system/app/enterprise/enterprise_attribute_escaping_e2e_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/enterprise/enterprise_attribute_escaping_e2e_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/enterprise/enterprise_attribute_escaping_e2e_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/enterprise/enterprise_attribute_escaping_e2e_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/enterprise/enterprise_attribute_escaping_e2e_spec.spl:149:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'escapes an attribute breakout in the CATALOG data-sku attribute' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/enterprise/enterprise_attribute_escaping_e2e_spec.spl:166:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'escapes an attribute breakout in the HCM data-employee attribute' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/enterprise/enterprise_attribute_escaping_e2e_spec.spl:183:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'escapes an attribute breakout in the PROC data-po attribute' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
