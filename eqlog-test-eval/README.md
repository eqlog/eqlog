This crate contains test that (supposedly) successfully compiled Eqlog programs behave as expected.

Run the same tests with either evaluation mode:

```sh
cargo test -p eqlog-test-eval
cargo test -p eqlog-test-eval --features naive
```
