# Trait method with a line-wrapped generic return type breaks the NEXT method

- Status: OPEN (2026-09-12)
- Component: parser (seed `src/compiler_rust`), trait declaration bodies
- Binary: `bin/release/aarch64-unknown-linux-gnu/simple`, sha256 `3d120a6f9ab5704b`
- Found by: L78-INT while integrating the L7/L8 V4 port packets

## Symptom

Inside a `trait` body, if a method's return type is wrapped across lines
(the generic argument list continues on the following line) AND another
method declaration follows it, the parser fails:

```
Unexpected token: expected Colon, found Me
```

The error names the file but no line, which is what made it expensive to
locate.

## Repro (fails)

```simple
pub trait T1:
    me roots(token: i64
        ) -> Result<i64,
                    text>
    me closure(token: i64) -> i64

pub fn main():
    print("ok")
```

`bin/simple run repro.spl` -> `error: compile failed: parse: ... expected Colon, found Me`

## Controls (all parse)

1. Same wrap, but the wrapped method is the LAST in the trait -> OK.
2. Same wrap in a free `fn` -> OK.
3. Same wrap in a `class` method followed by another method -> OK.
4. Trait method with a multi-line PARAMETER list (trailing comma included)
   and a single-line return type, followed by another method -> OK.

So the defect is specific to: trait body + wrapped return type + a
following member.

## Impact

`src/compiler/80.driver/cache/gateway/cooperative_namespace_gc_begin_authority_v1.spl`
did not parse at all, which made
`test/01_unit/compiler/cache/l78_namespace_port_v4_spec.spl`,
`l78_publication_port_v4_spec.spl` and `l78_pipeline_ports_v4_spec.spl`
report `outcome=ERROR executed=0`.

## Workaround applied (this is a workaround, not the fix)

The two wrapped return types in `L78NamespacePortV4` and its closed impl
were joined onto one line. The frozen API (names, parameters, result
shapes) is unchanged; only the source layout is. The parser still needs
the real fix.
