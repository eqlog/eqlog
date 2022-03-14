// #[macro_use] extern crate eqlog_util;
extern crate eqlog_util;
use eqlog_util::eqlog_mod;
eqlog_mod!(category);
eqlog_mod!(group);

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        let result = 2 + 2;
        assert_eq!(result, 4);
    }
}
