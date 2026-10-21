use crate::member_spaces::MemberSpaces;

/// Native rules can filter virtual members without expanding a dense bitmap.
#[derive(Clone, Copy)]
pub enum CanonicalMask<'a> {
    Dense(&'a [bool]),
    Members(&'a MemberSpaces),
}

impl CanonicalMask<'_> {
    pub fn contains(&self, handle: u32) -> bool {
        match self {
            Self::Dense(canonical) => canonical[handle as usize],
            Self::Members(spaces) => spaces.root(handle) == Some(handle),
        }
    }
}
