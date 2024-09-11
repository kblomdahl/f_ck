use criterion::{black_box, criterion_group, criterion_main, Criterion};
use std::io::{Stdin, Stdout};
use f_ck::{Compiled, Parsed};

const E: &[u8] = include_bytes!("../examples/e.bf");
const FIB: &[u8] = include_bytes!("../examples/fib.bf");
const MANDELBROT: &[u8] = include_bytes!("../examples/mandelbrot.bf");

fn bench_compiled(c: &mut Criterion, name: &str, program: &[u8]) {
    c.bench_function(&format!("parsed::{}", name), |b| {
        b.iter(|| Parsed::try_from(black_box(program)));
    });

    c.bench_function(&format!("compiled::{}", name), |b| {
        let parsed = Parsed::try_from(program).expect("could not parse program");

        b.iter(|| Compiled::<Stdin, Stdout>::from(black_box(&parsed)))
    });
}

pub fn criterion_benchmark(c: &mut Criterion) {
    bench_compiled(c, "e", E);
    bench_compiled(c, "fib", FIB);
    bench_compiled(c, "mandelbrot", MANDELBROT);
}

criterion_group!(compiled, criterion_benchmark);
criterion_main!(compiled);
