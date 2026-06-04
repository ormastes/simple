# Web Stack Sample Design

## Entities

- `SampleUser`
  - `id`, `username`, `email`, `password_hash`, `created_at`
- `SampleItem`
  - `id`, `user_id`, `title`, `details`, `created_at`, `updated_at`

## UI Surface

- `GET /login` and `GET /register` render plain HTML forms.
- `GET /items` renders the authenticated list page.
- `GET /items/new` and `GET /items/:id/edit` render one shared item form.
- `GET /items/search` uses a GET form so the Simple browser adapter can verify
  the generated query URL deterministically.

## Stable Markers

- `data-test="page-title"`
- `data-test="login-page-marker"`
- `data-test="login-success-marker"`
- `data-test="created-item-marker"`
- `data-test="search-result-marker"`

## Backend Behavior

- SQL uses `DbCodec<T>` + `Repository<T>`.
- Simple DB uses `SimpleDbRecordAdapter<T>` row mappers.
- Search parity is intentionally implemented in the shared app layer by loading
  records and filtering by field text so both backends behave the same.
