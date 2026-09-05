- Comments and commit messages should explain "why", not "what".
  Don't paraphrase code next to the comment.
- If you write code, you should commit your changes.
- No unicode (e.g. emojis, em dashes) in comments, code, commit messages etc.
  Only if needed to test unicode support etc.
- Most features should have tests.
  Prefer integration tests via eqlog-test-eval/ and eqlot-test-compile/ over unit tests.
- For enums other than `Option`, use exhaustive `match` expressions listing every variant; no wildcard/default arms, `if let`, `let ... else`, or `matches!`.
  `Option` checks such as `if let Some(...)` are allowed.
- Prefer fewer branches and shallow nesting.
- You should almost never ignore errors:
  Prefer failing over continuing in degraded state in most cases.
  When an error is expected in normal operation, be as specific about the error as possible.
  E.g. when reading a file that is not expected to exist, ignore only not found errors but not others.
- No local imports (use inside function bodies).
  Place all imports at module level.
- Multiline strings: Use indoc, formatdoc, printdoc etc.
- Format strings: Prefer the format!("{var}") variant over format!("{}", v).
  Introduce variables if necessary, e.g. let var = var.display(); for paths.
- Prefer explicit control flow over anyhow macros like bail! and ensure!.
- Review your patch sets.
  You usually want to spawn a subagent for this.
  Check which files you touched, then invoke git diff once per file.
  Things to look out for:
  Is the latest version internally consistent?
  Clean up left-overs from earlier iterations.
  Comments should describe the code as it exists in the current version, not a change.
  Lean towards writing too few comments rather than too many.
