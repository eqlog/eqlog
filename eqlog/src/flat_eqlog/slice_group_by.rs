/// A stripped-down copy of the standard libary std::slice::group_by function, which as of this
/// writing is not stable yet.
use std::mem;

#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct GroupByMut<'a, T: 'a, P> {
    slice: &'a mut [T],
    predicate: P,
}

impl<'a, T: 'a, P> GroupByMut<'a, T, P> {
    pub(super) fn new(slice: &'a mut [T], predicate: P) -> Self {
        GroupByMut { slice, predicate }
    }
}

impl<'a, T: 'a, P> Iterator for GroupByMut<'a, T, P>
where
    P: FnMut(&T, &T) -> bool,
{
    type Item = &'a mut [T];

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.slice.is_empty() {
            None
        } else {
            let mut len = 1;
            let mut iter = self.slice.windows(2);
            while let Some([l, r]) = iter.next() {
                if (self.predicate)(l, r) {
                    len += 1
                } else {
                    break;
                }
            }
            let slice = mem::take(&mut self.slice);
            let (head, tail) = slice.split_at_mut(len);
            self.slice = tail;
            Some(head)
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        if self.slice.is_empty() {
            (0, Some(0))
        } else {
            (1, Some(self.slice.len()))
        }
    }
}

pub fn slice_group_by_mut<'a, T, F>(slice: &'a mut [T], pred: F) -> GroupByMut<'a, T, F>
where
    F: FnMut(&T, &T) -> bool,
{
    GroupByMut::new(slice, pred)
}
