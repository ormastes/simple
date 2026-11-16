# Production V6 MAC comparison regression

Status: AUTHORED_NOT_RUN. Two executable scenarios invoke the actual production
MAC tag and verification functions. Each accepts its unchanged tag and refuses
all 64 individual valid-hex tag mutations. The second uses a canonical failed
operation reply and checks that authentication preserves its nonzero exit code.

These assertions do not simulate native owners or prove native timing behavior.
They do not reproduce the concurrent `rt_black_box` fallback race: the separate
runtime regression owns that test and its source repair. A fixed-width loop or
its pure OR guard cannot repair the shared native volatile sink's C data race.
The integrated authentication source depends on the reviewed function-local
volatile fallback repair, preserving the existing GNU assembly branch and ABI.

Native concurrency, optimized assembly, timing, parser/type checking, and live
client/server execution remain NOT_RUN. No existing accepted protocol fixture
or immutable snapshot is changed by this added regression.
