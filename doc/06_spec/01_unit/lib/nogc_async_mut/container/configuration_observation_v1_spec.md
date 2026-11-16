# Container configuration observation V1

Executable source: `test/01_unit/lib/nogc_async_mut/container/configuration_observation_v1_spec.spl`.

Status: **AUTHORED_NOT_RUN**, seven cases. Scripted facts exercise production common API/adapters/runtime/parser; they are not native observations or platform qualification.

1. `Observe the admitted native ID through the common API and three fixed backend captures`: prepare and recover an actual scripted Windows owner, read configuration through the common API, and assert actual argv (spaces, empty argument and Unicode), workdir, false ROFS, ordered duplicate environment names/digests, image identity distinction, complete mount entry and no secret values in the public wire. The canonical-wire decoder also refuses a changed workdir with the original content digest. Returned owner has consumed the expected 14 scripted commands.
2. `Change Path between the two actual container query completions`: assert no observation and configuration-changed refusal while preserving the updated owner.
3. `Return the right image config ID with an unrelated manifest digest`: assert missing RepoDigests correspondence refuses even though the actual image/config ID matches.
4. `Supply a plan digest that does not match the original retained request`: assert pre-query refusal and unchanged script cursor.
5. `Use the production strict parser through the retained owner`: assert duplicate JSON keys and excessive nesting refuse with constant diagnostics that do not disclose environment values.
6. `Use multiple native mount entries, including a read-only named volume`: assert every mount is preserved and 65 entries refuse instead of truncating.

7. `Request actual full-log capture from the actual scripted common owner`: assert actual capture is explicitly unavailable, no EOF receipt is minted from script text, and the updated owner retains its expected cursor after current-container validation.

The fixture uses the existing common API quarantine/admission/create/recovery flow before configuration reads. It deliberately uses a failed post-create observation followed by exact retained-ID recovery; it supplies no caller readiness flag. The separate parser assertion is DATA validation, not a replacement evidence producer.

Pending native fixture: run these exact fixed queries against admitted Linux Podman and Windows Docker resources, validate their actual image mapping, config changes, inherited environment defaults and mounted-volume projection. No runtime, compiler, Docker, Podman or kernel namespace test has run here. Full-log EOF and cleanup evidence is a separate owner port; this manual makes no stream-completeness claim.

Actual capture prerequisite: accepted IO R2 requires Linux native main-thread process origin or the Windows canonical native thread. Wrong-thread/fork/namespace refusal is not a successful capture. No worker-thread or legacy-capture fallback is provided.
