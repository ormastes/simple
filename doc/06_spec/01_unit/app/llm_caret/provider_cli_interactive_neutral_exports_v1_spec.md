# Interactive neutral export compatibility

Status: AUTHORED_NOT_RUN. Compiler/native/task execution is NOT_COVERED.

An app-imported request is passed directly to the neutral root planner, and its
result is consumed as the app-imported nominal PlanData type. Exact root argv
still accepts literal `-`, keeps `--help` positional, and rejects old versions.
There is no conversion factory, task launch or capability construction.

The accepted interactive9 unit and actual-selection DATA fixture continue through
the app compatibility exports. The latter exercises the neutral intent builder's
same opaque selection/receipt types after composition; it remains NOT_RUN and
does not establish TaskRef access, invocation grants or a terminal owner.
