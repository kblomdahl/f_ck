use criterion::{black_box, criterion_group, criterion_main, Criterion};
use std::io::Cursor;
use f_ck::{execute, Compiled, Context, Parsed};

const QUICKSORT: &[u8] = include_bytes!("../examples/quicksort.bf");

pub fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function("quicksort", |b| {
        let parsed = Parsed::try_from(QUICKSORT).expect("could not parse program");
        let compiled = Compiled::from(&parsed);

        b.iter(|| {
            let mut context = Context {
                output: vec! [],
                input: Cursor::new(QUICKSORT),
            };

            execute(&mut context, black_box(&compiled))
        });
    });
}

criterion_group!(dispatch, criterion_benchmark);
criterion_main!(dispatch);
