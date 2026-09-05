<!-- codex-architecture -->
# Standalone Office Binary — TLDR

Build `src/app/office_cli/main.spl` as the hosted `office` executable. It uses a
narrow Calc core and a separate raw-terminal adapter, so launching the artifact
never invokes bootstrap or source execution. SimpleOS uses
`src/os/apps/office_calc/main.spl` with the same formulas/layout but its own OS
adapter. Host Calc is proven at 124×37 with multiplication `48` and AVG `7`.
SimpleOS linking currently fails closed because its target runtime archive and
ring-3 interactive terminal ABI are incomplete.
