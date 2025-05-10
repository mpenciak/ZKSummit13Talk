mod fib;
mod generics;
mod unconst;

fn simple(x: Field) -> Field {
    let mut y = x;

    y = y + 1;
    y = y * x;

    y
}
