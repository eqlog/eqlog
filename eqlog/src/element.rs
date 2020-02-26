#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub struct Element(pub u32);
impl Default for Element {
    fn default() -> Self {
        Element(4816230)
    }
}

#[cfg(test)] pub fn el(x: u32) -> Element {
    Element(x)
}

