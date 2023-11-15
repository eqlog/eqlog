use std::fmt::{Display, Formatter, Result};

pub struct FmtFn<F: Fn(&mut Formatter) -> Result>(pub F);

impl<F: Fn(&mut Formatter) -> Result> Display for FmtFn<F> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        self.0(f)
    }
}
