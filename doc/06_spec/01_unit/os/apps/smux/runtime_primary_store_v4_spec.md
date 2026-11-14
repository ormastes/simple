# smux primary V4 archives

Source: `test/01_unit/os/apps/smux/runtime_primary_store_v4_spec.spl`.
Status: **NOT_RUN**. Manually authored companion, not generated execution evidence.

Three scenarios use real private temporary directories and pure primary-plan
fixtures: request/plan roundtrip and distinct namespaces; changed valid request,
mode, and plan-digest conflict refusal with original bytes preserved; correlation
mutation refusal before publication. Fixtures have no live provider or session.

These checks do not cover configured server planning, signed helper execution,
native opening, or post-effect owner retention.
