use std::static_assert;

unconstrained fn new() -> Field {
    5
}

fn test() {
    let x = unsafe {
        3
    };
    let y = new();
    assert_eq(x, y);
}
