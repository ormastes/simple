# Graph adapter behind devhub email sent GETs without auth, then crashed

Status: fixed 2026-10-31 on the interpreter seed. Found by the emulated mail spec.

`adapter_outlook.spl`, used by `devhub email` and `devhub outlook`, built requests with
`http_get(url)`. On the Phase 1 seed in interpret mode the request reached the server
immediately with no `Authorization` header, and the adapter then failed with
`tuple index access on non-tuple type object`. PATCH, built with `create_request`, was
correct. So every Graph GET failed, and a bearer-less request left the machine.

The likely cause is that the name resolves to something that sends rather than to the
tuple builder in `std.http_client`. That was inferred from the symptoms, not traced. The
native path was not tested.

The fix builds GET and POST with `create_request`. `http_delete` is imported but unused.

Specs in `test/03_system/app/devhub/feature/devhub_mail_emulated_spec.spl`:

- Reproduction: "lists messages through adapter_outlook".
- Generalisation: "reports 401 through adapter_outlook", "marks a message read with a PATCH".
