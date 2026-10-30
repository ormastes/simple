# Qualified export routes absent from worker source closure

Status: reviewed candidate; native and runner qualification pending.

Attempt 6 lowered 285 of 304 runner modules, leaving 19 BLOCKED, compared with
277 lowered and 27 BLOCKED in attempt 5. All three HIR workers completed;
neither log reported a CRASH module. The eight resolved modules do not justify
claiming complete runner admission. The remaining inventory includes
`src/lib/nogc_async_mut/env/__init__.spl`, which declares qualified exports such
as `export variables.env_get`.

The frozen resolver in `module_surface_registry_index.spl` builds export route
indices for qualified members, aliases and globs. The worker source scanner
previously recognized use/import/from-import/export-use/export-from but omitted
plain qualified exports. Thus its pre-parse closure can omit a provider which
the authoritative frozen readiness graph requires.

The candidate adds sibling and absolute qualifier candidates conservatively.
It does not change resolution precedence, inventory, readiness propagation or
BLOCKED handling. Actual contribution to all 19 blocked modules is unproven.

`worker_surface_qualified_route_probe.spl` invokes real filesystem closure,
parsing, frozen registry construction and readiness. It covers member, alias
and glob routes, requires an actual resolved edge, and checks that withholding
the provider blocks its facade. Local-only exports add no dependency.

Native execution is pending. Two bounded diagnostic build attempts used the
retained pure-Simple producer SHA256
`e3a7e65cdad2aea37939056f5f115053733e342a89f0507eaec3ede9212233d6`:

- `/tmp/simple-qualified-route-probe-20261030`: the old producer's own HIR
  closure remained incomplete; exit 1, peak 10,479,412 KiB, no artifact.
- `/tmp/simple-qualified-route-complete-probe-20261030`: explicitly recorded
  diagnostic exception `SIMPLE_HIR_WORKER_SKELETON=0`, complete inventory and
  unchanged checks, 300-second/48-GiB bounds. Receipt reports
  `rss-containment-unverified`, exit 89, peak 50,345,468 KiB against
  50,331,648 KiB. No artifact or runtime acceptance resulted.

These failures are not passing tests or new compiler qualification. Astra
reviewed the exact source and fixture with no P0/P1/P2 findings. The reviewed
candidate may enter the next isolated producer build; its native fixture and
real runner inventory must then be qualified before landing or claiming repair.
