# Public exec-control installation route

Status: **NOT_RUN**. Authored source specification, not execution evidence.
Requirements: ORCH-02 public command routing; HOST-02 authority owner boundary.

The public command is `host-exec-control-install <protected-root> <signed-packet-file>`.
The app forwards it to the existing Host domain and preserves both nested cleanup
fields through the existing owned reply path. The app performs no engine call,
policy installation, grant verification or journal write itself.

| Exact step | Actual checks |
|---|---|
| routes missing installation arguments to the actual host domain before opening owners | Invoke the public dispatcher; require the Host argument-count error and no created cleanup owner. |
| rejects extra installation arguments before reading caller paths | Invoke the public dispatcher with an extra argument; require the same Host refusal before either unused path is read. |

These cases require the actual Host installation consumer dependency. They do
not simulate a successful signed installation. Installation success denotes
installed configuration only; it does not authorize or report runtime exec.
