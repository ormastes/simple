# Format-on-Save Integration Guide

**Feature:** #910 - Canonical Formatter Editor Integration
**Status:** ✅ Complete
**Last Updated:** 2025-12-24

## Overview

The Simple formatter (`simple fmt`) provides automatic code formatting with a canonical, opinionated style. This guide shows how to integrate format-on-save into your development workflow.

## Prerequisites

Ensure `simple` is installed and available in your PATH:

```bash
# Verify installation
simple --version

# Test formatter
simple fmt --help
```

## Editor Integrations

### VS Code

#### Quick Setup

1. Install the Simple Language extension (if available)
2. Add to `.vscode/settings.json`:

```json
{
  "simple.formatOnSave": true,
  "simple.formatter.path": "/usr/bin/simple",
  "editor.formatOnSave": true,
  "[simple]": {
    "editor.defaultFormatter": "simple-lang.simple",
    "editor.formatOnSave": true
  }
}
```

#### Manual Setup (without extension)

Add a task to `.vscode/tasks.json`:

```json
{
  "version": "2.0.0",
  "tasks": [
    {
      "label": "Format Simple Code",
      "type": "shell",
      "command": "simple",
      "args": ["fmt", "${file}"],
      "problemMatcher": [],
      "presentation": {
        "reveal": "never"
      }
    }
  ]
}
```

Add a keybinding in `.vscode/keybindings.json`:

```json
[
  {
    "key": "ctrl+shift+f",
    "command": "workbench.action.tasks.runTask",
    "args": "Format Simple Code",
    "when": "editorLangId == 'simple'"
  }
]
```

### Vim/Neovim

#### Auto-format on Save

Add to `~/.vimrc` or `~/.config/nvim/init.vim`:

```vim
" Auto-format Simple files on save
autocmd BufWritePre *.spl silent! !simple fmt %

" Alternative: Use formatprg
autocmd FileType simple setlocal formatprg=simple\ fmt\ --stdin

" Format command (optional)
command! SimpleFmt !simple fmt %

" Keybinding for manual format
autocmd FileType simple nnoremap <buffer> <leader>f :!simple fmt %<CR>
```

#### With ALE (Asynchronous Lint Engine)

```vim
" Add to .vimrc
let g:ale_fixers = {
\   'simple': ['simple_fmt'],
\}
let g:ale_fix_on_save = 1

" Define the fixer
function! ale#fixers#simple_fmt#Fix(buffer) abort
    return {
    \   'command': 'simple fmt --stdin'
    \}
endfunction
```

#### With Neovim LSP

If using Neovim with LSP:

```lua
-- init.lua or ftplugin/simple.lua
vim.api.nvim_create_autocmd("BufWritePre", {
  pattern = "*.spl",
  callback = function()
    vim.fn.system("simple fmt " .. vim.fn.expand("%"))
    vim.cmd("edit")  -- Reload file
  end,
})

-- Or use vim.lsp.buf.format() if LSP supports formatting
vim.api.nvim_create_autocmd("BufWritePre", {
  pattern = "*.spl",
  callback = function()
    vim.lsp.buf.format({ timeout_ms = 2000 })
  end,
})
```

### Emacs

Add to `~/.emacs` or `~/.emacs.d/init.el`:

```elisp
;; Simple mode hook for formatting
(add-hook 'simple-mode-hook
  (lambda ()
    (add-hook 'before-save-hook 'simple-format nil t)))

;; Format function
(defun simple-format ()
  "Format the current buffer using simple fmt."
  (interactive)
  (when (eq major-mode 'simple-mode)
    (let ((current-point (point)))
      (shell-command-on-region
        (point-min) (point-max)
        "simple fmt --stdin"
        (current-buffer) t
        "*simple fmt errors*" t)
      (goto-char current-point))))

;; Keybinding (optional)
(define-key simple-mode-map (kbd "C-c C-f") 'simple-format)
```

#### With LSP Mode

```elisp
(use-package lsp-mode
  :hook ((simple-mode . lsp))
  :config
  (lsp-register-client
   (make-lsp-client
    :new-connection (lsp-stdio-connection "simple-lsp")
    :major-modes '(simple-mode)
    :server-id 'simple-lsp)))

;; Enable format on save
(add-hook 'simple-mode-hook
  (lambda ()
    (add-hook 'before-save-hook 'lsp-format-buffer nil t)))
```

### Sublime Text

Create a build system in `Tools > Build System > New Build System`:

```json
{
  "cmd": ["simple", "fmt", "$file"],
  "file_regex": "^(.+):([0-9]+):([0-9]+): (.+)$",
  "selector": "source.simple",
  "quiet": true
}
```

Save as `Simple Format.sublime-build`.

For auto-format on save, install Package Control and LSP plugin, then configure the LSP client for Simple.

### IntelliJ IDEA / CLion

1. Go to `Settings > Tools > File Watchers`
2. Click `+` to add new watcher
3. Configure:
   - **Name:** Simple Formatter
   - **File type:** Simple (or create custom type for `.spl`)
   - **Scope:** Current File
   - **Program:** `simple`
   - **Arguments:** `fmt $FilePath$`
   - **Output paths:** `$FilePath$`
   - **Working directory:** `$ProjectFileDir$`
   - **Advanced Options:**
     - ✅ Auto-save edited files to trigger the watcher
     - ✅ Trigger watcher on external changes
4. Apply and OK

## Git Integration

### Pre-commit Hook

Format files automatically before each commit.

Create `.git/hooks/pre-commit`:

```bash
#!/bin/sh
# Format all staged Simple files before commit

echo "Running Simple formatter on staged files..."

# Get all staged .spl files
files=$(git diff --cached --name-only --diff-filter=ACM | grep '\.spl$')

if [ -z "$files" ]; then
    exit 0
fi

# Format each file
for file in $files; do
    if [ -f "$file" ]; then
        simple fmt "$file"
        git add "$file"
    fi
done

echo "✓ Formatted $(echo "$files" | wc -l) file(s)"
exit 0
```

Make it executable:

```bash
chmod +x .git/hooks/pre-commit
```

### Pre-commit Framework

Using [pre-commit](https://pre-commit.com/):

Create `.pre-commit-config.yaml`:

```yaml
repos:
  - repo: local
    hooks:
      - id: simple-fmt
        name: Simple Formatter
        entry: simple fmt
        language: system
        files: \.spl$
        pass_filenames: true
```

Install and run:

```bash
pip install pre-commit
pre-commit install
pre-commit run --all-files  # Initial format
```

### Husky (for Node.js projects)

If your project uses npm/yarn:

```bash
npm install --save-dev husky lint-staged
npx husky install
npx husky add .husky/pre-commit "npx lint-staged"
```

Add to `package.json`:

```json
{
  "lint-staged": {
    "*.spl": "simple fmt"
  }
}
```

## CI/CD Integration

### GitHub Actions

Create `.github/workflows/format.yml`:

```yaml
name: Format Check

on:
  pull_request:
    paths:
      - '**.spl'
  push:
    branches: [main, develop]

jobs:
  format:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3

      - name: Install Simple
        run: |
          # Add installation steps for Simple compiler
          curl -sSL https://get.simple-lang.org | sh
          echo "$HOME/.simple/bin" >> $GITHUB_PATH

      - name: Check formatting
        run: simple fmt --check src/

      - name: Show diff if formatting needed
        if: failure()
        run: |
          simple fmt --diff src/
          echo "::error::Files need formatting. Run 'simple fmt src/' locally."
```

### GitLab CI

Add to `.gitlab-ci.yml`:

```yaml
format-check:
  stage: test
  image: simple-lang/simple:latest
  script:
    - simple fmt --check src/
  only:
    - merge_requests
    - main
  except:
    changes:
      - "*.md"
      - "docs/**"
```

### CircleCI

Add to `.circleci/config.yml`:

```yaml
version: 2.1
jobs:
  format-check:
    docker:
      - image: simple-lang/simple:latest
    steps:
      - checkout
      - run:
          name: Check formatting
          command: simple fmt --check src/
workflows:
  version: 2
  test:
    jobs:
      - format-check
```

### Jenkins

```groovy
pipeline {
    agent any

    stages {
        stage('Format Check') {
            when {
                changeRequest()
            }
            steps {
                sh 'simple fmt --check src/'
            }
        }
    }
}
```

## Project-Level Configuration

### Make Integration

Add to `Makefile`:

```makefile
.PHONY: fmt fmt-check

# Format all Simple files
fmt:
	@echo "Formatting Simple code..."
	@find src -name "*.spl" -exec simple fmt {} \;
	@echo "✓ Done"

# Check formatting (CI mode)
fmt-check:
	@echo "Checking Simple code formatting..."
	@simple fmt --check src/ || (echo "Run 'make fmt' to fix formatting" && exit 1)
```

Usage:

```bash
make fmt        # Format all files
make fmt-check  # Check formatting (CI)
```

### Justfile Integration

Using [just](https://github.com/casey/just):

```justfile
# Format all Simple files
fmt:
    find src -name "*.spl" -exec simple fmt {} \;

# Check formatting without modifying
fmt-check:
    simple fmt --check src/

# Format specific file
fmt-file FILE:
    simple fmt {{FILE}}
```

## Watch Mode (Development)

### Using `watchexec`

Install [watchexec](https://github.com/watchexec/watchexec):

```bash
# Watch and format on file changes
watchexec -e spl --clear 'simple fmt src/'

# With custom ignore patterns
watchexec -e spl -i 'test/**' -i 'build/**' 'simple fmt src/'
```

### Using `entr`

```bash
# Watch and format changed files
find src -name "*.spl" | entr simple fmt /_
```

### Using `fswatch` (macOS)

```bash
fswatch -o src/**/*.spl | xargs -n1 -I{} simple fmt src/
```

## LSP Integration (Future)

When the Simple Language Server (`simple-lsp`) supports formatting:

### Generic LSP Client Configuration

```json
{
  "languageServer": {
    "simple": {
      "command": "simple-lsp",
      "filetypes": ["simple"],
      "rootPatterns": ["simple.toml", ".git"],
      "settings": {
        "simple": {
          "formatOnSave": true,
          "formatter": {
            "maxLineLength": 100,
            "indentSize": 4
          }
        }
      }
    }
  }
}
```

## Troubleshooting

### Formatter Not Found

```bash
# Check if simple is in PATH
which simple

# Or use full path in editor config
/usr/local/bin/simple fmt %
```

### Formatting Fails Silently

```bash
# Test formatter manually
simple fmt your_file.spl

# Check for syntax errors
simple fmt --check your_file.spl
```

### File Not Reloading After Format

For Vim:

```vim
" Add autoread to .vimrc
set autoread
autocmd BufWritePost *.spl checktime
```

For Emacs:

```elisp
;; Enable auto-revert
(global-auto-revert-mode 1)
```

### Format Takes Too Long

```bash
# Format specific files instead of entire directories
simple fmt $(git diff --name-only --diff-filter=ACM | grep '.spl$')
```

## Best Practices

1. **Commit `.editorconfig`** with formatter settings for team consistency
2. **Enable format-on-save** in your primary editor
3. **Use pre-commit hooks** to catch unformatted code early
4. **Run format check in CI** to enforce formatting in PRs
5. **Format entire codebase** before enabling CI checks:
   ```bash
   simple fmt src/
   git commit -am "Format all code with simple fmt"
   ```

## Related Documentation

- [Formatter Specification](spec/formatter.md) - Complete formatting rules
- [Simple CLI Reference](CLI.md) - All `simple fmt` options
- [Contributing Guide](CONTRIBUTING.md) - Code style for contributors

## Support

If you encounter issues:

1. Check `simple fmt --help` for latest options
2. Test formatting manually before adding automation
3. Report bugs at https://github.com/simple-lang/simple/issues

## Examples

### Format on Save + Lint on Save

**VS Code:**

```json
{
  "editor.formatOnSave": true,
  "editor.codeActionsOnSave": {
    "source.fixAll": true
  }
}
```

**Vim with ALE:**

```vim
let g:ale_linters = {'simple': ['simple-lint']}
let g:ale_fixers = {'simple': ['simple_fmt']}
let g:ale_fix_on_save = 1
let g:ale_lint_on_save = 1
```

### Multi-File Format

```bash
# Format all files in src/
simple fmt src/

# Format specific files
simple fmt file1.spl file2.spl file3.spl

# Format git-modified files
git diff --name-only | grep '\.spl$' | xargs simple fmt

# Format with glob pattern
simple fmt src/**/*.spl
```

---

**Feature Status:** ✅ Complete (#910)
**Last Updated:** 2025-12-24
**Maintainer:** Simple Language Team
