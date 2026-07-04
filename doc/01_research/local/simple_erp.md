# Local Research: Simple ERP

- Update 2026-07-03: the standalone repo now exists and tracks this submodule:
  https://github.com/ormastes/simple-erp (pushed from examples/12_business/simple_erp).

- No existing ERP example or ERP submodule was found before this lane.
- `https://github.com/ormastes/simple-erp.git` was checked and returned
  repository-not-found at the time, so the example started as a local submodule at
  `examples/12_business/simple_erp`.
- Related reusable examples exist:
  - `examples/06_io/restaurant_webapp` for restaurant ordering and payment views.
  - `examples/11_advanced/simple_db` for database-oriented example structure.
  - `src/lib/nogc_async_mut/payment` for payment infrastructure.

Decision: create an isolated `examples/12_business/simple_erp` submodule seed
instead of folding this into unrelated dirty work or referencing a missing
remote.
