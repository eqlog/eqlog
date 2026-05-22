Verify your commits.
This includes:
- tests
- cargo fmt --check
- Review your changes relative to the merge base of your upstream.
  You usually want to spawn a subagent for this.
  Check which files you touched, then invoke git diff once per file.
  Things to look out for:
  Is the latest version internally consistent?
  Clean up left-overs from earlier iterations.
  Comments should describe the code as it exists in the current version, not a change.
  Doc comments should describe the contract the function promises to its callers, not its implementation details.
  Comments are typically needed to add context to a code snippet, but are not needed when they just paraphrase code they appear next to.
