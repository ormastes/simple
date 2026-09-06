# Web layout manager agent tasks

| Lane | Scope | Owner |
|---|---|---|
| Interface/design | Contracts and design artifacts | Root merge owner |
| Invalidation | Classifier and stable frontier | Small-agent lane |
| Oracle adapter | Browser snapshot conversion and text port | Small-agent lane |
| Manager/spec | Framework delegation and executable evidence | Root merge owner |

Final reviewer: root normal-capability review. Renderer integration is serial after the interface checkpoint; agents must not edit shared renderer files concurrently.

