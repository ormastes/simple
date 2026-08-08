# Local Research: Simple ERP

- No existing ERP example or ERP submodule was found before this lane.
- `https://github.com/ormastes/simple-erp.git` was checked and returned
  repository-not-found, so the example is registered as a local submodule at
  `examples/12_business/simple_erp`.
- Related reusable examples exist:
  - `examples/06_io/restaurant_webapp` for restaurant ordering and payment views.
  - `examples/11_advanced/simple_db` for database-oriented example structure.
  - `src/lib/nogc_async_mut/payment` for payment infrastructure.

Decision: create an isolated `examples/12_business/simple_erp` submodule seed
instead of folding this into unrelated dirty work or referencing a missing
remote.
