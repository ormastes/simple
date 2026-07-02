<!-- llm-process-gen: managed source=pipe_impl_dev_skill source_sha256=fbb0fb94bfcdd3eea90270a94b94d6bc1bf3f6e24872b0ee735c681af331dcd2 content_sha256=fbb0fb94bfcdd3eea90270a94b94d6bc1bf3f6e24872b0ee735c681af331dcd2 -->
# /dev

Development command for quick iteration and testing.

## Usage
```
/dev [task_description]
```

## Purpose
Fast development loop for incremental changes without full pipeline overhead.

## When to use
- Small bug fixes
- Quick feature iterations
- Experimental changes

## Notes
This is a lightweight development shortcut. For production work, use the full pipeline: /research → /design → /impl → /verify → /release
