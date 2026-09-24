# Bug — `bin/simple ui web <file.ui.sdn>` exits before binding

Date: 2026-09-24. Found by lane L6 (shared cross-lane pieces) during
rendering-showcases verification.

## Symptom

`bin/simple ui web examples/06_io/ui/hello_web.ui.sdn --port 8080`

- Rust seed binary (`bin/simple`, with `SIMPLE_LIB=src`): exits silently at
  ~6 s, before binding the port. Reproduced with the shipped
  `hello_web.ui.sdn`, so it is not the new `rendering_items.ui.sdn`.
- Pure-Simple release binary (`bin/release/aarch64-apple-darwin/simple`):
  dies immediately with no output (also stale — see the check-worker bug of
  the same date).

## Impact

REQ-001 (web-server GUI) cannot go green: the UI-base switch's `web` branch
honest-fails with `showcase status=blocked web reason=server-exited-early`,
and no `.ui.sdn` can be served by `src/app/ui.web/server.spl` on this
checkout until this is fixed or the self-hosted binary is redeployed.

## Expected

The WebServer binds the requested port, serves the rendered UISession HTML,
and holds the loop until killed; a bounded TCP probe succeeds.

## Reproduce

```sh
SIMPLE_LIB=src bin/simple ui web examples/06_io/ui/hello_web.ui.sdn --port 8080 &
sleep 10; nc -z 127.0.0.1 8080 || echo "not bound"
```
