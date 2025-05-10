fn fib<let N: u32>() -> Field {
    let mut a: Field = 0;
    let mut b: Field = 1;

    for _ in 0..N {
        let temp = a;
        a = b;
        b = temp + b;
    }

    a
}

