# TypeScript/JavaScript Language Agent

**Language:** TypeScript, JavaScript
**File extensions:** `.ts`, `.tsx`, `.js`, `.jsx`, `.mjs`, `.cjs`
**LSP server:** `tsserver` (TypeScript Language Server) via `typescript-language-server`

---

## Build & Test Commands

```bash
# Node.js / npm
npm install                         # Install dependencies
npm run build                       # Build project
npm test                            # Run tests
npx tsc --noEmit                    # Type-check without emitting

# Bun (alternative runtime)
bun install
bun run build
bun test

# Testing frameworks
npx jest                            # Jest
npx vitest                          # Vitest
npx mocha                           # Mocha

# Linting & formatting
npx eslint .                        # Linter
npx prettier --write .              # Formatter
npx prettier --check .              # Check formatting
```

## LSP Setup

Install the TypeScript language server:
```bash
npm install -g typescript typescript-language-server
```

Ensure `tsconfig.json` exists in the project root for proper type resolution.

## Style Rules

- **TypeScript preferred:** use `.ts`/`.tsx` over `.js`/`.jsx` for new code
- **Strict mode:** enable `strict: true` in `tsconfig.json`
- **Naming:** `camelCase` for variables/functions, `PascalCase` for types/classes/components
- **Imports:** use ES module syntax (`import/export`); avoid `require` in TypeScript
- **Types:** prefer interfaces over type aliases for object shapes; avoid `any`
- **Null handling:** use strict null checks; prefer optional chaining (`?.`) and nullish coalescing (`??`)
- **Async:** use `async/await` over raw Promises; handle errors with try/catch
- **React (if applicable):** functional components with hooks; avoid class components
- **Formatting:** follow project ESLint/Prettier config; 2-space indent is standard

## When To Use This Agent

Dispatch this agent when the task involves:
- Writing or editing `.ts`, `.tsx`, `.js`, `.jsx` files
- Node.js applications or CLI tools
- React/Vue/Svelte frontend code
- npm package development
- MCP server implementations in TypeScript
- Web dashboard or browser-side code
- Configuration files (`tsconfig.json`, `package.json`)
