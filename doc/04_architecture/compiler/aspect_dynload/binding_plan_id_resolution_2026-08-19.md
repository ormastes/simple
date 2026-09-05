# Resolution: JoinpointRoute.binding_plan_id (design §11.1)

Date: 2026-08-19. Scope: decide whether the sole absent JoinpointRoute field,
`binding_plan_id`, is implementable today or blocked on §22.4 Binding IR.
Source design: `doc/05_design/language/aop/aspect_facet_dynload_smf_pack_design_2026-08-04.md`.

## 1. Verbatim design evidence

The token `binding_plan_id` appears exactly ONCE in the entire design, as a bare
field name in the §11.1 JoinpointRoute record layout (line 963):

```text
### JoinpointRoute

joinpoint_slot_id
pack_id
aspect_id
binding_plan_id
activation_mode
```

No sentence anywhere in the document defines, constrains, or assigns this field.

The phrase "binding plan" (as prose) appears exactly ONCE, in §14.4 (line 1235),
about open-world business-interface bindings:

> "The binding plan contains the business interface ID. Every loaded module
> publishes type descriptors and implemented-interface IDs."

§22.4 Binding IR (line 1579) defines the only structure named "*BindingPlan*":

```simple
struct FacetBindingPlan:
    aspect_id: AspectId
    facet_interface_id: TypeId
    target_predicate: TypePredicateBytecode
    implementation_id: TypeId
    representation: Attached | NominalStatic
    multiplicity: Single | Multi
    access: FacetAccess
    required: bool
```

Note: `FacetBindingPlan` has NO id field, and it is a FACET plan — §22.4 defines
no advice/joinpoint binding-plan struct at all, even though `binding_plan_id`
lives on the JOINPOINT route, not the facet route (§11.1 FacetRoute has no
`binding_plan_id`).

Supporting context:
- §11.1 (line 968): the catalog answers "Which pack owns dynamic join-point
  slot 817?" — routing only; "It is not sufficient to execute the aspect;
  detailed symbols and relocations remain in the pack."
- §11.2 (lines 984, 1002): the pack directory carries `BindingSummaryEntry[]`
  and ModuleEntry has `binding_summary_range` — but neither is defined
  field-by-field, and nothing links them to `binding_plan_id`.
- §11.3 (line ~1030): "full pointcut/binding bytecode" lives INSIDE compressed
  module chunks.
- §14.1 AdviceBindingRegistry: "Maps prepared join-point slots to static,
  startup, or dynamic advice chains" — keyed by slot, not by plan id.

## 2. Reading

Is it (a) an identifier into a build-time-computed binding plan produced by
§22.4 Binding IR, or (b) a runtime-resolvable id the loader could compute?

The design supports only (a), and even that incompletely. Everything with
"binding"/"plan" semantics is produced at BUILD time by the §22 pipeline
(§22.4 Binding IR structs; §22.6 outputs "binding summary metadata in ordinary
aspect-module SMF"). The catalog is explicitly routing-only, so
`binding_plan_id` can only be a foreign key from the app catalog into
build-emitted binding artifacts inside the pack — most plausibly an index/id
into the pack's `BindingSummaryEntry[]` or the module-chunk binding bytecode.
It cannot be loader-computed: the loader never sees §22.4 IR, and the design
gives the loader no rule to derive any such id.

But the design NEVER states: (1) the id's referent (BindingSummaryEntry index?
a plan record in chunk bytecode? something else?); (2) its namespace (per-pack?
per-aspect? global?); (3) who assigns it; (4) any advice-side plan struct it
could identify — §22.4 defines only `FacetBindingPlan`, id-less and
facet-scoped. Inventing any of these would be guessing.

## 3. Tree evidence

`grep -rn "binding_plan\|BindingPlan\|plan_id" src/` — NO aspect/AOP binding-plan
concept exists. All hits are unrelated namesakes:
- `src/lib/common/wine_nt_import.spl:18,28,44,...` — `WineNtHelloImportBindingPlan`
  etc. (Wine PE import binding).
- `src/compiler/60.mir_opt/hwir_opt/riscv_scalar_binding.spl:20,50` and
  `resource_binding.spl:6` — `HwirRiscvScalarBindingPlan` /
  `HwirResourceBindingPlan` (hardware IR resource binding).
- `src/lib/common/aspect_pack.spl` — implements JoinpointRoute routing
  (`:40,79,258,1104`) but contains no `binding_plan` token at all.

Nothing implements §22.4 Binding IR (`FacetBindingPlan` has zero occurrences in
`src/`).

## 4. Verdict: BLOCKED-ON-BINDING-IR

`binding_plan_id` is a build-time-assigned foreign key into binding-plan
artifacts that the §22.4 Binding IR / §22.6 packaging pipeline must emit — and
that pipeline does not exist. The field is not runtime-derivable and is
correctly ambiguous today; do not populate it with an invented value.

What must land first, in order:
1. An advice/joinpoint counterpart to `FacetBindingPlan` in §22.4 (the design
   currently defines none), with an explicit `plan_id` field and a stated id
   namespace (recommended: per-pack, assigned by the pack builder).
2. A field-level definition of §11.2 `BindingSummaryEntry` stating whether
   `binding_plan_id` indexes it.
3. §22.6 packaging emitting those records, so the catalog writer has a real id
   to copy into JoinpointRoute.

Until then the checklist item should read: "absent by design-incompleteness —
blocked on §22.4 Binding IR; design must specify referent, namespace, and
assigner." A placeholder of 0 = "no plan emitted yet" is the only honest
implementable value today, and only if documented as such.
