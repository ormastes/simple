# Protected Windows Controller root scenarios

AUTHORED_NOT_RUN. No native runtime, Simple test, build or deployment was run.

The executable specification invokes actual installation, existing Windows private
root/journal ownership, shared replay, current validation and native close. It
requires Windows and a dedicated administrator-provisioned private root supplied
as `SIMPLE_WINDOWS_CONTROLLER_PRIVATE_ROOT`. The two public fixture paths
`SIMPLE_WINDOWS_CONTROLLER_CONFIG_FILE` and `SIMPLE_WINDOWS_CONTROLLER_POLICY_FILE`
contain a valid canonical V3 config and matching existing authority policy. Missing
fixtures fail; they do not skip or construct opaque owners.

1. Install exact immutable public bytes, project the actual Windows-backed
   Controller journal, confirm the decoded Controller identity, close, reject a
   stale copied owner, then reopen by exact digest. This tests storage only; the
   config's Host binding is not claimed to be an opened or authorized Host.
2. Use a different digest against the populated fixture. The operation must refuse
   with `controller-local-config-pin` and return the acquired native cleanup owner.

The fixture does not delete its immutable records. Use dedicated isolated roots.
It stops on native cleanup errors and reports them; a failed harness cannot retain
capabilities after its process exits. Actual close fault injection and recovery,
ancestor substitution, policy mutation under native handles, partial publication,
Controller/Host simultaneous ownership, signed dispatch, service-incarnation
resume, and real Docker inspection are NOT_COVERED by these two cases. They remain
required integrated scenarios after the nonterminal service composition is chosen.
