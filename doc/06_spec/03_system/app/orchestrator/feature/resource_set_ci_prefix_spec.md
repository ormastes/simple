# ResourceSet CI prefix preservation

Source: `test/03_system/app/orchestrator/feature/resource_set_ci_prefix_spec.spl`.
Status: **NOT_RUN**. Authored manual; no generated/runtime evidence.

Use existing ci_job_process.sdn and ci_pipeline.sdn fixtures. Compare Job values
through the legacy and unified singleton entrypoints and Pipeline values through
a nested ResourceList. Invalid backoff and runPolicy retain exact root paths
and gain spec.items.0 prefixes when nested, with original positive source
coordinates. Unknown and duplicate keys remain rejected at the strict boundary.
This checks schema values only; no CI task, host or provider executes.
