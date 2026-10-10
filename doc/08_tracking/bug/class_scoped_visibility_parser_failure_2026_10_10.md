# Class scoped visibility stops WEB native compilation

Status: OPEN (P1)

Actual a0 source/aa404 producer WEB closure fails worker_owner229, h2_connection116, worker_wire36 at pub(package) me/static/field declarations. The class parser consumed pub only, leaving the parenthesis for the class member dispatcher. The top-level visibility owner already consumes this syntax and returns package. Source repair shares that owner and stores its exact result on methods. Tests are AUTHORED_UNEXECUTED.

Field syntax qualification is separate from field access control: CoreDecl retains field names/types/defaults/bits but no field visibility array, and flat_parser_field_from_nodes constructs Visibility.Private. This existing metadata loss is not repaired or qualified here. Unknown textual scopes retain the existing top-level warning/public recovery policy; malformed delimiter/nonidentifier regressions assert parser errors. No source visibility workaround or widening to pub was applied.
