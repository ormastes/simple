# Image-to-Markdown with LLM Caret and SPipe

The image reader uses a separate, explicit vision profile. Text-chat settings never authorize image transmission.

## Local Slang or OpenAI-compatible model

Add this section to the LLM Caret SDN config:

```sdn
image_read:
  profile_id: local-vision
  provider: slang
  base_url: http://localhost:8721
  model: <served-vision-model-id>
  model_revision: <pinned-revision>
  location: local
  egress: deny
  vision: true
  structured_output: true
  detail: high
  max_images: 5
  max_pixels: 40000000
  max_request_bytes: 20971520
  max_output_tokens: 16384
  timeout_ms: 30000
  max_concurrency: 1
  trust_scope: workspace
```

For Ollama, vLLM, or another OpenAI-compatible local server, use `provider: openai_compat` and its loopback `base_url`. The declared model must actually accept OpenAI-style typed image content.

## Hosted API profile

Use `provider: openai` or `provider: claude_api`, set `location: remote` and `egress: allow`, and name the secret environment variable with `api_key_env`. Do not put the key value in the SDN file. There is no implicit local/remote fallback.

```sdn
image_read:
  profile_id: hosted-vision
  provider: openai
  base_url: https://api.openai.com
  model: <vision-model-id>
  model_revision: <pinned-revision>
  api_key_env: OPENAI_API_KEY
  location: remote
  egress: allow
  vision: true
  structured_output: true
  detail: high
  max_images: 5
  max_pixels: 40000000
  max_request_bytes: 20971520
  max_output_tokens: 16384
  timeout_ms: 30000
  max_concurrency: 1
  trust_scope: workspace-private
```

Complete config-file reloads reset omitted image settings to fail-closed local
defaults, so an earlier egress grant or API-secret reference cannot leak into a
later profile. For hosted OpenAI or Claude profiles, an unset/empty referenced
environment variable returns typed `missing_secret` before provider transport.

## SPipe

Set `image_read_profile: <profile_id>` on the explicit image-to-Markdown action. If it is absent, SPipe returns `skipped: image_read_profile not configured` and performs zero model calls. A mismatched, text-only, unsafe-egress, oversized, or unsupported profile fails before transmission.

Run the canonical SPipe action with:

```sh
bin/simple run src/app/spipe/main.spl -- image-read \
  --config llm_caret.sdn --profile local-vision \
  --image input.png --root . --output build/image-data --name input \
  --spec test/03_system/app/my_app/feature/my_feature_spec.spl
```

When `--spec` is present, SPipe publishes a bounded evidence sidecar binding
the source, Markdown, structured extraction, and receipt hashes. Omitting it
runs conversion without attaching evidence to a spec.

The direct application entry is `src/app/image_to_markdown/main.spl` and takes
the same arguments except `--profile`. Local-file admission accepts PNG, JPEG,
and WebP by signature, validates bounded container headers and decoded
dimensions, and never trusts a filename extension. The proxy uses the same
provider-neutral inspector: PNG checks every chunk CRC, JPEG requires SOI/EOI
and a bounded SOF marker, and WebP validates RIFF plus VP8/VP8L/VP8X headers.
Unsupported or malformed formats fail closed.

The Caret `/v1/chat/completions` and `/v1/messages` proxy routes preserve
ordered multimodal parts. OpenAI and Anthropic image shapes are converted at
the provider boundary, Anthropic top-level system text is retained, and image
requests always use the exact configured image profile rather than text-chat
endpoint settings.
Hosted HTTPS requests use the shared certificate-verifying browser H1/TLS
transport with one aggregate deadline and no redirect following; admitted
loopback Slang requests use the native HTTP v2 transport.

## Output

The human artifact is Markdown with page inventory, original-script text/handwriting, tables/forms, charts, high-definition numeric arrays, uncertainty, unresolved content, and provenance. A synchronized receipt records hashes and model/prompt/schema/preprocessing identity without secrets or raw image bytes.

Use `$image-read` for the interactive workflow and review its linked Markdown/receipt rather than trusting a chat summary.
