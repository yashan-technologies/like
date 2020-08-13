// Copyright 2020 CoD Team. All Rights Reserved.

use criterion::{black_box, criterion_group, criterion_main, Criterion};
use like::{ILike, Like};

fn bench_like<T: Like + ?Sized>(c: &mut Criterion, input: &T, pattern: &T, id: &str, nid: &str) {
    c.bench_function(id, |bench| bench.iter(|| black_box(input.like(pattern))));
    c.bench_function(nid, |bench| {
        bench.iter(|| black_box(input.not_like(pattern)))
    });
}

fn bench_ilike<T: ILike + ?Sized>(c: &mut Criterion, input: &T, pattern: &T, id: &str, nid: &str) {
    c.bench_function(id, |bench| bench.iter(|| black_box(input.ilike(pattern))));
    c.bench_function(nid, |bench| {
        bench.iter(|| black_box(input.not_ilike(pattern)))
    });
}

fn bench_str_like(c: &mut Criterion) {
    bench_like(c, "hello, world!", "hello%", "like_str", "not_like_str");
}

fn bench_bytes_like(c: &mut Criterion) {
    let input = &b"hello, world!"[..];
    bench_like(c, input, b"hello%", "like_bytes", "not_like_bytes");
}

fn bench_str_ilike(c: &mut Criterion) {
    bench_ilike(c, "hello, world!", "HellO%", "ilike_str", "not_ilike_str");
}

fn bench_bytes_ilike(c: &mut Criterion) {
    let input = &b"hello, world!"[..];
    bench_ilike(c, input, b"HellO%", "ilike_bytes", "not_ilike_bytes");
}

criterion_group!(
    like_bench,
    bench_str_like,
    bench_bytes_like,
    bench_str_ilike,
    bench_bytes_ilike,
);
criterion_main!(like_bench);
