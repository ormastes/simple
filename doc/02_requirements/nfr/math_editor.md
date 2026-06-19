# LibreOffice Math NFR Requirements

## Requirements

- MATH-NFR-001: Math rendering is pure Simple logic with no filesystem, shell,
  browser, GUI, CAS, or network calls.
- MATH-NFR-002: Token processing uses iteration-based access and avoids indexed
  array reads on token lists.
- MATH-NFR-003: MathML output is deterministic and escapes user-controlled token
  text.
- MATH-NFR-004: The LLM catalog advertises only Math structures backed by
  implemented and tested APIs.
