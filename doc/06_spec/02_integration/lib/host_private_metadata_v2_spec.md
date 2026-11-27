# Installed metadata through native Windows private owners

Source: `test/02_integration/lib/host_private_metadata_v2_spec.spl`.
Evidence: all five scenarios **NOT_RUN**. No Windows execution or platform
qualification is claimed. The companion was reviewed from authored source.

The real Windows runner must have an independently provisioned native-private
directory in `SIMPLE_HOST_METADATA_PRIVATE_PARENT`. The negative ACL case
requires `SIMPLE_WINDOWS_PRIVATE_FOREIGN_READ_ROOT`, provisioned with foreign
read access. Missing fixtures fail; these cases do not skip on Linux or replace
ACL evidence with POSIX modes. Synthetic public data is installed by native
exclusive staging, sealing and publication beneath a fresh native child.

1. Read four retained file generations, refresh those exact handles and close
   them before deliberate reopen. No service-readiness assertion is made.
2. Supply a wrong broker pin and refuse metadata. A later correct open proves
   that ordinary failure cleanup released all four admitted file generations.
3. Omit the fourth file, require admission failure and then reopen/read the
   first file to check that prior partial admissions were closed.
4. Change a retained owner's pin, require refresh to return no owner/metadata,
   retain any pending cleanup and verify copied native file values cannot read.
5. Refuse the independently provisioned foreign-readable root through the
   actual native private owner.

Failed-close injection is not claimed by these loader scenarios. Canonical
generation invalidation and native failed-close retention remain shared-owner
contracts with their separate authored evidence. The complete dependency
graph is assembled by root; the cleanup helper is not copied into this lane.
