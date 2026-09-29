<!-- llm-process-gen: managed source=gemini_sync_skill source_sha256=2f9d4bf427a6a875f0e162661da3f31d4647be3f9159da54eec4e0a22e836efc content_sha256=1a3ccd8c61708f2e71ad6dbccba183feacd1828e3e80cfcb43957c5a239b61ff -->
# sync

Source: `.gemini/commands/sync.toml`

Pull, rebase, and push with file-count safety checks. Worktree-aware jj sync.

Reject main-worktree mutation, stale target SHA, branch/workspace ownership mismatch, unconditional force, and broad ref pushes.
