# Parser never terminates on a `_reserved: 27` bitfield field

- **Status:** open

The documented bitfield form (docstrings in
`src/compiler/10.frontend/parser_types.spl:468` and
`src/compiler/20.hir/hir_definitions.spl:329`) ends with a bare-width
reserved field:

    bitfield Flags(u32):
        enabled: bool
        priority: u4
        _reserved: 27

`parse_full_frontend` on that text reports `expected type annotation` /
`bitfield field type must be bool, uN, or iN` / `duplicate bitfield field
name: 27` and then repeats the same errors without advancing; a spec using
it hit the 900 s child timeout. Either the documented syntax should parse or
the error path must consume the token. Reproduced under the seed-run
self-hosted frontend on 2026-10-10.
