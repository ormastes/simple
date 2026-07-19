# devhub `web_storage` (alias `storage`) — mc-style facade

Research basis: real `mc` binary (`RELEASE.2025-08-13T08-35-41Z`) — help
captured live. `aws` CLI not installed on the research host, so no side-by-side
`aws s3` comparison was possible; `mc` is the sole ground truth. This is a
**greenfield facade** design layered on top of the existing `itf minio`
subcommand family in `src/app/itf/`.

---

## 1. Ground truth: `mc` grammar

```
mc [FLAGS] COMMAND [COMMAND FLAGS | -h] [ARGUMENTS...]
```

Relevant top-level commands: `alias`, `cp`, `cat`, `du`, `ls`, `mb`, `rb`,
`rm`, `mirror`, `share`, `stat`. Global flags: `--json` (JSON-lines output),
`--quiet`/`-q` (no progress bar), `--no-color`, `--config-dir`/`-C` (alias
store location, default `~/.mc`), `--insecure` (skip TLS verify — a flag the
repo's pure-Simple transport explicitly cannot honor, see §4).

**Addressing model** (the mc idiom this facade must mirror): every path is
either a bare local filesystem path, or `ALIAS/bucket[/key...]`. Aliases are
named, stored server endpoints:

```
mc alias set <alias> <URL> <ACCESS-KEY> <SECRET-KEY>
mc alias list
mc alias remove <alias>
```

Per-subcommand USAGE (verbatim from `mc <cmd> --help`):

| Subcommand | USAGE |
|---|---|
| `ls`     | `mc ls [FLAGS] TARGET [TARGET ...]` |
| `cp`     | `mc cp [FLAGS] SOURCE [SOURCE...] TARGET` |
| `cat`    | `mc cat [FLAGS] TARGET [TARGET...]` |
| `stat`   | `mc stat [FLAGS] TARGET [TARGET ...]` |
| `mb`     | `mc mb [FLAGS] TARGET [TARGET...]` |
| `rb`     | `mc rb [FLAGS] TARGET [TARGET...]` |
| `rm`     | `mc rm [FLAGS] TARGET [TARGET ...]` |
| `share`  | `mc share COMMAND [COMMAND FLAGS] [ARGUMENTS...]` — sub-verbs `download` (presigned GET), `upload` (presigned POST policy / curl form), `list`/`ls` |
| `mirror` | `mc mirror [FLAGS] SOURCE TARGET` |
| `du`     | `mc du [FLAGS] TARGET` |

Notable mc UX conventions to mirror:
- `cp`/`mirror` direction is inferred purely from which side is a local path
  vs. `alias/bucket/...` — no explicit `--upload`/`--download` flag.
- `--recursive`/`-r` is the universal "act on a prefix" flag (`ls`, `cp`,
  `stat`, `rm`, `du` all take it).
- `du --depth N` truncates the recursive summary to N levels; `du` with no
  flags gives one aggregate line.
- `stat --verbose` on a bucket-level target gives bucket metadata instead of
  per-object; plain `stat` on a bucket recurses into contents.
- Humanized sizes/dates are the default rendering; `--json` switches to
  JSON-lines. mc has no `--bytes`-style raw-integer flag — that convenience is
  unique to `itf minio`, worth keeping in the facade.
- `share upload` is a distinct sub-verb from `share download` (confirmed live
  via `mc share --help`'s top-level listing; `mc share upload --help` itself
  was not run). From general knowledge of mc it emits a `curl -F ...` command
  against a presigned POST *policy* (multi-field form), not a single presigned
  PUT URL — a meaningfully different flow from this repo's `presign-put` (a
  bare presigned PUT URL for `curl -X PUT --data-binary`). Flagged as
  knowledge-sourced, not verified against this host's `mc`.

---

## 2. Existing repo implementation

Three relevant files, all in `src/app/itf/`:

**`cmd_minio.spl`** (373 lines) — wired CLI, dispatched from `main.spl` as
`itf minio` / `itf mio`. Subcommands today: `ls [bucket [--prefix P]]`, `get
<bucket> <key> [--out PATH] [--range R]`, `put <bucket> <key> --file PATH
[--content-type CT]`, `stat <bucket> <key>`, `presign <bucket> <key>
[--expires N]`, `presign-put <bucket> <key> [--expires N]`, `mb <bucket>`,
`rb <bucket>`, `health`. Flags: `--json`, `--bytes` (raw byte counts vs.
`format_size` humanization), `--no-pager`. No `rm` (object delete), no `du`,
no `mirror`, no `cat` as a distinct verb (get without `--out` already prints
body to stdout, functionally `cat`).

**`adapter_minio.spl`** (809 lines) — pure-Simple SigV4/REST implementation,
zero shell-out, zero `mc` dependency. Fn inventory: `load_minio_config`,
`check_minio_auth`, `minio_list_buckets`, `minio_list_objects` (single
prefix, no true recursion — one level via ListObjectsV2), `minio_get_object`,
`minio_download`, `minio_head_object`, `minio_stat_object`, `minio_put_text`
(≤64 MiB UTF-8 bodies), `minio_put_object` (binary PUT — hard stub, see §4),
`minio_create_bucket`, `minio_delete_bucket`, `minio_presign_get`,
`minio_presign_put`, `minio_health_live`. **Config is single-endpoint**:
`_parse_minio_section` reads exactly one `[minio]` section from
`~/.config/itf/auth.sdn` (url, region, access_key, secret_key,
tls_skip_verify) — no multi-alias concept today.

**`adapter_minio_mc.spl`** (405 lines) — a second, separate adapter that
shells to the real `mc` binary via `process_run` and parses `--json` NDJSON
output. Fn inventory: `mc_alias_set/remove/list`, `mc_ls`, `mc_stat`,
`mc_get`, `mc_put` (via `mc cp`, so — unlike `minio_put_object` — legitimately
handles binary uploads since it shells to real `mc`), `mc_share_download`
(presign), `mc_admin_info`, `mc_health_ready`. Its `McClient` class carries
`alias_name` + `mc_path` (default `"mc"`) and `_qualify_path(alias, path)`
already builds exactly the `alias/bucket/key` addressing mc itself uses.

**Critical finding, confirmed by grep: `adapter_minio_mc.spl` has no caller
anywhere in `main.spl`/`cmd_minio.spl`** — it is dead code from the
dispatcher's point of view (confirmed in `.claude/skills/minio.md` prose too:
"exists but is not wired into dispatch"). Raw `mc` is only invoked today via a
documented manual escape hatch, never through `itf`/`bin/itf` code paths.

Also absent from **both** adapters (confirmed via grep, zero hits): object
delete (`rm`), disk-usage summary (`du`), `mirror`, and an `mb`/`rb` wrapper
in the mc adapter (raw `mc mb`/`mc rb` exist as commands but
`adapter_minio_mc.spl` never builds argv for them). `share upload` (presigned
POST policy) also has no wrapper in either adapter — only `share download`
(→ `mc_share_download`) is wrapped.

---

## 3. Facade grammar

```
devhub storage <verb> [alias/][bucket[/key...]] [flags]
devhub web_storage ...            # full name, same dispatch
```

`storage` is registered next to `web_storage` exactly the way `itf minio`
already has `mio` as a short alias in `main.spl` (`"minio" | "mio":`) — same
pattern, one more string in the match arm.

**Assumption made explicit** (not specified either way by the source task):
this design treats `devhub` as a new top-level command name whose
`storage`/`web_storage` subcommand reuses `itf`'s existing adapters in
place — not a rename of `itf` itself and not a new binary reimplementing
SigV4 from scratch. Every adapter fn below (`minio_*`, `mc_*`) lives in
`src/app/itf/`; wiring `devhub storage` to them means either (a) `devhub`
becomes a thin second dispatcher in the same build importing `cmd_minio`'s
helpers directly, or (b) `devhub` is a new alias registered in `main.spl`'s
existing match arm — the mapping table below is correct under either choice;
only entry-point wiring differs, confirm which before coding.

### Verb → adapter mapping

| Verb | Grammar | Adapter mapping | Status |
|---|---|---|---|
| `ls` | `storage ls [alias[/bucket[/prefix]]] [-r\|--recursive] [--bytes] [--json]` | no-arg → `minio_list_buckets`; with bucket → `minio_list_objects` (SigV4 path); `-r` on a prefix → **gap**, `minio_list_objects` has no recursion knob, would need to fall back to `mc_ls(recursive: true)` via the mc adapter (wire it in) | Partial — bucket-level ls exists; recursive needs the mc-adapter fallback wired in |
| `cp` | `storage cp SRC DST [-r] [--content-type CT]` (direction inferred from which side has a local path vs `alias/bucket/key`) | local→remote text: `minio_put_text`; local→remote binary: **gap**, `minio_put_object` is a hard stub → auto-fallback to `mc_put` (mc adapter, wire in) or print the `presign-put` workaround if `mc` absent; remote→local: `minio_download`/`minio_get_object` | Partial — text upload + all downloads work; binary upload needs the mc fallback or presign-put workaround |
| `cat` | `storage cat alias/bucket/key [--range R]` | `minio_get_object` (print `.body`, same as `itf minio get` without `--out`) | Exists (already how `cmd_minio._minio_get` behaves sans `--out`) |
| `stat` | `storage stat alias/bucket/key [--bytes] [--json]` | `minio_stat_object` — **note**: not a real HEAD; approximated via ListObjectsV2 exact-key filter because `rt_http_request` exposes no response headers, so ETag/Last-Modified come from the LIST body, not a HEAD response | Exists, with a documented fidelity caveat |
| `mb` | `storage mb alias/bucket` | `minio_create_bucket` | Exists |
| `rb` | `storage rb alias/bucket [--force]` | `minio_delete_bucket` (empty-bucket only; `--force` recursive-empty-then-delete is **gap**, mc's `rb --force` semantics aren't wrapped) | Partial |
| `rm` | `storage rm alias/bucket/key [-r]` | **gap** — no `minio_delete_object` in either adapter today; needs new SigV4 `DELETE` call in `adapter_minio.spl` (sign+send `DELETE` to the object path, S3 returns 204) or an `mc_rm` argv builder added to the mc adapter | Gap — smallest net-new addition needed for the facade to be useful day one |
| `presign` (mc: `share download`) | `storage presign alias/bucket/key [--expires N]` | `minio_presign_get` (client-side, no network round-trip) or `mc_share_download` | Exists |
| `presign-put` (mc: `share upload`, different mechanism — see §1) | `storage presign-put alias/bucket/key [--expires N]` | `minio_presign_put` — a bare presigned PUT URL, deliberately simpler than mc's multi-field POST-policy form; keep this repo's simpler shape rather than copying mc's `curl -F` output, say so in `--help` | Exists, intentionally divergent from mc |
| `mirror` | `storage mirror SRC TARGET [--dry-run]` | **gap** — no equivalent in either adapter; would need either a new loop of `ls` + `cp` calls in the facade layer itself (simplest, reuses existing primitives) or an `mc mirror` argv wrapper | Gap |
| `du` | `storage du alias/bucket[/prefix] [--depth N]` | **gap** — no equivalent in either adapter; simplest implementation is client-side: page through `minio_list_objects` and sum `size`, no new SFFI needed | Gap, but cheap to close (pure aggregation over existing `ls`) |
| `health` | `storage health [alias] [--json]` | `minio_health_live` or `mc_health_ready` | Exists |

---

## 4. Alias/config model — the biggest structural gap

mc's alias store (`~/.mc/config.json`, multiple named endpoints) has no
equivalent in `adapter_minio.spl`: `load_minio_config` parses exactly one
`[minio]` section from `~/.config/itf/auth.sdn`. To honor mc-shaped
`alias/bucket/key` addressing for real (multiple named endpoints, not just
one implicit default), `auth.sdn` needs either:
- multiple bracketed sections, e.g. `[minio.prod]` / `[minio.staging]`, with
  `_parse_minio_section` extended to take a section-name parameter and
  `load_minio_config` extended to `load_minio_config(alias: text)`; or
- delegate alias storage entirely to `mc`'s own `~/.mc/config.json` via
  `mc_alias_list`/`mc_alias_set` (already-built argv builders in
  `adapter_minio_mc.spl`) and have the facade read that as its alias source
  of truth when `mc` is installed, falling back to a single implicit
  `default` alias backed by the existing single `[minio]` section when it
  isn't.

Given `adapter_minio_mc.spl` already has working `mc_alias_set/list/remove`
argv builders sitting unused, the second option is less new code — but it
makes `storage`'s alias list `mc`-dependent unless the first option (extend
`auth.sdn`) is also done as the no-`mc` fallback. Recommend supporting both:
`mc`-backed aliases when `mc --version` succeeds, `auth.sdn`-section-backed
single alias (`default`) otherwise — mirroring the existing "SigV4 primary,
mc CLI escape hatch" split documented in `.claude/skills/minio.md`.

---

## 5. Output conventions

- Humanized by default: reuse `output.spl::format_size` (KiB/MiB/GiB) and the
  existing table renderer `print_table_dynamic` for `ls`; `--bytes` flag
  (already in `itf minio ls`/`stat`) stays as the raw-integer escape hatch —
  a nicety mc itself lacks (mc always humanizes, no raw-bytes flag), worth
  keeping as a repo-specific improvement over mc.
- `format_transfer_summary` (already used in `cmd_minio._minio_get`/
  `_minio_put`) gives the up/down transfer-rate line for `cp`.
- `wants_json`/`format_json_output` cover `--json` uniformly, matching mc's
  own `--json` global flag semantics (JSON-lines, one object per line for
  multi-result verbs like `ls`).

---

## 6. Error cases + exit codes

Mirrors `cmd_minio.spl`'s existing convention: 0 success, 1 failure, no other
codes in use anywhere in `itf`.

| Case | Behavior | Exit |
|---|---|---|
| No `[minio]`/alias config, or missing access/secret key | `print_error("MinIO auth not configured...")`, same message class as `_require_auth` | 1 |
| `tls_skip_verify: true` in config | Hard-fail before any request — `_require_transport`'s existing security-lie guard, reused verbatim | 1 |
| Binary `cp`/`put` with no `mc` installed and no `--presign-put` fallback chosen | Clear message naming both escape hatches (`presign-put` + curl, or install `mc`), same phrasing as `minio_put_object`'s existing error string | 1 |
| `rm`/`du`/`mirror` invoked before the gaps above are closed | `print_error("storage <verb>: not yet implemented — <one-line reason + link to workaround>")`, never a silent no-op | 1 |
| Object/bucket not found | Passed through from `map_s3_error` (already parses S3 XML error bodies in `adapter_minio.spl`) | 1 |
| Network/transport error | Passed through raw transport error text, retried up to `ITF_RETRY_MAX_ATTEMPTS` (3, exponential 2/4/8s, `Retry-After`-aware) before surfacing | 1 |
| Unknown verb | `print_error("unknown storage command: {verb}")` + help text, same shape as `handle_minio`'s `_:` arm | 1 |
| Success | `print_success(...)` + optional `--json` | 0 |

---

## 7. Summary: new vs. reused

**Reused as-is**: bucket ls, object ls (single-prefix), get/cat, download,
stat (with documented HEAD-via-LIST caveat), text put, mb, rb (empty-bucket),
presign-get, presign-put, health, retry policy, humanized-size output,
`--json`/`--bytes` conventions, error-mapping from S3 XML.

**Smallest net-new work to make the facade day-one useful**: (1) object
`rm` — one new signed DELETE call, the only S3 verb genuinely missing
end-to-end; (2) client-side `du` — pure aggregation over existing
`minio_list_objects`, no new SFFI; (3) wiring `adapter_minio_mc.spl` into
dispatch at all (currently zero callers) so binary `cp`/recursive `ls` can
fall back to it instead of dead-ending on `minio_put_object`'s stub.

**Structural decision needed before real multi-alias support**: single vs.
multi-endpoint config (§4) — today's `auth.sdn` models exactly one MinIO
target, so `alias/bucket/key` addressing is only cosmetically mc-shaped until
either `auth.sdn` grows named sections or the facade delegates alias storage
to `mc`'s own config file.

**Deliberately not copied from mc**: `share upload`'s multi-field
presigned-POST-policy/curl-form flow — the repo's simpler bare
presigned-PUT-URL (`presign-put`) is a smaller, already-working surface and
should stay that way rather than chasing mc's exact output shape.
