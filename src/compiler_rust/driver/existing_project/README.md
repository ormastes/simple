# existing_project

A Simple language web application.

## Building

```bash
simple web build app.sui -o public/
```

## Running

```bash
cd public/
python3 -m http.server 8000
```

Then open http://localhost:8000/app.html

## Structure

- `app.sui` - Main application file (server + client + template)
- `public/` - Built assets (HTML, WASM, manifest)

## Learn More

- Simple Web Framework: https://docs.simple-lang.dev/web
- .sui File Format: https://docs.simple-lang.dev/sui
