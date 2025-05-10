pub struct Pairs<I> {
    a: I,
    b: I,
}

pub trait HasFirst<I> {
    pub fn first(self) -> I;
}

impl<I> HasFirst<I> for Pairs<I> {
    fn first(self) -> I {
        self.a
    }
}

