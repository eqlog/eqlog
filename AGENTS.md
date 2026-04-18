Verify your commits.
This includes:
- tests
- cargo fmt --check
- eqlog-eqlog should have prebuilt rust committed.
  Make sure to regenerate with `eqlog eqlog-eqlog/src eqlog-eqlog/prebuilt/` if necessary.
- Manually review.
  No spurious changes, comments describe code as is (not your change).
  Review file by file by inspecting git diff, usually relative to merge base with your upstream.
