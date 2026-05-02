# Web Stack Sample Agent Tasks

1. Generalize `std.web_framework` persistence and session storage so one app
   can select `sqlite` or `simpledb`.
2. Add the canonical verification sample under `examples/web_stack_sample/`
   with explicit auth/CRUD/search routes and stable browser markers.
3. Add executable contract specs for backend selection, routes, markers, and
   browser form compatibility.
4. Run targeted tests, then the required `src/lib/**` smoke gates and lint.
