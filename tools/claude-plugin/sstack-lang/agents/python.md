# Python Language Agent

**Language:** Python
**File extensions:** `.py`, `.pyi`
**LSP server:** `pylsp` (python-lsp-server) or `pyright`

---

## Build & Test Commands

```bash
# Virtual environment
python3 -m venv .venv
source .venv/bin/activate

# Install dependencies
pip install -r requirements.txt
pip install -e .                    # Editable install

# Testing
pytest                              # Run all tests
pytest path/to/test_file.py        # Single file
pytest -k "test_name"              # Single test by name
pytest --cov=src                   # With coverage

# Linting & formatting
ruff check .                        # Fast linter
ruff format .                       # Formatter
mypy src/                           # Type checking
black .                             # Alternative formatter
flake8 .                            # Alternative linter
```

## LSP Setup

Install `python-lsp-server`:
```bash
pip install python-lsp-server[all]
```

Or use `pyright` for faster, stricter type checking:
```bash
npm install -g pyright
```

## Style Rules

- **PEP 8:** follow PEP 8 conventions; use formatter (ruff/black) to enforce
- **Type hints:** annotate all function signatures; use `typing` module for complex types
- **Naming:** `snake_case` for functions/variables, `CamelCase` for classes, `UPPER_CASE` for constants
- **Imports:** group as stdlib / third-party / local; use absolute imports
- **Docstrings:** use Google or NumPy style; document parameters, returns, and exceptions
- **Error handling:** use specific exception types; avoid bare `except:`
- **Dependencies:** pin versions in `requirements.txt`; use `pyproject.toml` for packages
- **Python version:** default to 3.10+ unless project specifies otherwise

## When To Use This Agent

Dispatch this agent when the task involves:
- Writing or editing `.py` / `.pyi` files
- Python scripts, tools, or utilities
- ML/data science code (PyTorch, NumPy, pandas)
- Python packaging and distribution
- Python test suites (pytest, unittest)
- Type stub generation
