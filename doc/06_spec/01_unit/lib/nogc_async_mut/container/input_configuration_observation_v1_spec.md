# Input configuration observation V1

Source: `test/01_unit/lib/nogc_async_mut/container/input_configuration_observation_v1_spec.spl`.
Status: **AUTHORED_NOT_RUN**, seven source scenarios. Actual native/compiler/
runtime/engine execution remains NOT_RUN under the existing exhausted cap.

The fixture prepares and recovers a real scripted Windows common owner through
the existing quarantine/admission/create/recovery API, then supplies scripted
engine facts to its production executor. These facts are not a native grant or
qualification. No caller observation DTO is passed to the new producer.

1. `Read the admitted original request through the same actual scripted common owner`:
   assert actual false OpenStdin/Tty, true recorded StdinOnce, ordered effective
   argv/environment names, private environment values absent from the wire,
   canonical round trip and the updated owner's expected fourteen-command cursor.
2. `Refuse each unavailable boolean before issuing the image query`: missing
   OpenStdin/Tty/StdinOnce, null, string and numeric facts all refuse explicitly;
   the returned owner stops after twelve commands rather than defaulting false.
3. `Recheck OpenStdin Tty and the record-only StdinOnce fact`: changing any flag
   between the two container captures refuses even when V1 configuration matches.
4. `Bind input observations to the original admitted request digest`: an altered
   original plan refuses before another native query and retains the nine-command
   owner produced by the setup.
5. `Wrong native generation and image metadata cannot acquire a wrapper`: retain
   the existing runtime-generation, image/config-ID and repository correspondence
   refusals through the new producer.
6. `Use the production strict parser through the actual common owner`: duplicate,
   unknown and excessively nested native fields refuse with no raw text leakage.
7. `Compare the unchanged V1 producer with the V1 component of the new actual producer`:
   compare canonical wire/digest from both actual API entries; the legacy fixed
   command is unchanged. A changed outer OpenStdin fact without a new digest fails.

Native fixture still required: run the same fixed queries against actual admitted
Windows Docker and legacy Linux Podman resources, including absent/nonboolean
schema behavior and changes between captures. Check real current-create-to-start
restriction, charge and cleanup through its genuine Host owner separately.

Fresh Linux is explicitly unsupported until its own actual producer is installed:
`linux-fresh-workload-input-configuration-unavailable`, same owner retained, no
legacy-journal fallback. The genuine fresh-owner refusal fixture is owned by the
Linux owner worker. It is **NOT_COVERED** by this pure/scripted spec; no synthetic
native capability or disabled passing test is used as a substitute.

StdinOnce is observational. These configuration booleans do not prove EOF, kernel
stdin descriptor state, launch admission, task freshness or positive Argv support.
