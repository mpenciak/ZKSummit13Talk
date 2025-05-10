pub struct Pair<I> {
    a: I,
    b: I,
}

impl<I> Pair<I> {
    fn make(a: I, b: I) -> Pair<I> {
        Pair { a, b }
    }

    fn make_diag(a: I) -> Pair<I> {
        Pair { a, b: a }
    }
}

fn these_equal(a: Field) -> bool {
    let p_1 = Pair::make(a, a);
    let p_2 = Pair::make_diag(a);
    (p_1.a == p_2.a) & (p_1.b == p_2.b)
}
