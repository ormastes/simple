# Interpreter call-ladder prevention controls

Executable source: `test/01_unit/interpreter/call_ladder_miss_path_prevention_spec.spl`.
Status: authored manual; current-source Simple execution and docgen are **NOT_RUN**.

The five cases invoke actual interpreter call shapes: an imported ordinary function and a local function return their expected values; a module-level decorator doubles the original result; a nested decorator adds ten; a function-typed parameter named `str` takes precedence over the prelude builtin; and an undecorated name remains callable after other functions are decorated.

The module-level `@twice` declaration sets the process-global decorator flag before the scenarios execute. Therefore the ordinary-call scenarios establish lookup correctness with that flag already set. They do **not** prove the cold false-flag shortcut, nor its performance. The nested case checks the resulting wrapper behavior; it cannot independently prove that its sentinel writer was the first writer to enable the global flag.

The fixed expected values are 3 and 42 for ordinary calls, 12 for each decorated result, `n=7` for the shadowing parameter, and 2 for the final undecorated call. These are semantic assertions, not a claim that every priority branch or error path has been exercised.

Verification waiting: run this spec through the admitted interpreter environment and retain actual execution evidence. A separate fresh-process no-decorator control is required to qualify the cold false-flag branch. Rust sampler-owner tests and RSS gate selftests do not execute these Simple call scenarios.
