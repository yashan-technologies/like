// Copyright 2020 CoD Technologies Corp.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use criterion::{black_box, criterion_group, criterion_main, Criterion};
use like::{Escape, ILike, Like};

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

fn bench_escape<T: Escape + ?Sized>(c: &mut Criterion, input: &T, esc: &T, id: &str) {
    c.bench_function(id, |bench| bench.iter(|| black_box(input.escape(esc))));
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

fn bench_str_escape(c: &mut Criterion) {
    bench_escape(c, "hello$_world!", "$", "escape_str");
}

fn bench_bytes_escape(c: &mut Criterion) {
    let input = &b"hello$_world!"[..];
    bench_escape(c, input, b"$", "escape_bytes");
}

criterion_group!(
    like_bench,
    bench_str_like,
    bench_bytes_like,
    bench_str_ilike,
    bench_bytes_ilike,
    bench_str_escape,
    bench_bytes_escape,
);
criterion_main!(like_bench);
