// Copyright 2020-2021 CoD Technologies Corp.
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

use bencher::{benchmark_group, benchmark_main, black_box, Bencher};
use like::{Escape, ILike, Like};

fn bench_str_like(bench: &mut Bencher) {
    bench.iter(|| {
        let _n = Like::<true>::like(black_box("hello, world!"), black_box("hello%"));
    })
}

fn bench_str_not_like(bench: &mut Bencher) {
    bench.iter(|| {
        let _n = Like::<true>::not_like(black_box("hello, world!"), black_box("hello%"));
    })
}

fn bench_str_ilike(bench: &mut Bencher) {
    bench.iter(|| {
        let _n = ILike::<true>::ilike(black_box("hello, world!"), black_box("Hello%"));
    })
}

fn bench_str_not_ilike(bench: &mut Bencher) {
    bench.iter(|| {
        let _n = ILike::<true>::not_ilike(black_box("hello, world!"), black_box("Hello%"));
    })
}

fn bench_bytes_like(bench: &mut Bencher) {
    bench.iter(|| {
        let _n = Like::<true>::like(black_box(&b"hello, world!"[..]), black_box(&b"hello%"[..]));
    })
}

fn bench_bytes_not_like(bench: &mut Bencher) {
    bench.iter(|| {
        let _n =
            Like::<true>::not_like(black_box(&b"hello, world!"[..]), black_box(&b"hello%"[..]));
    })
}

fn bench_bytes_ilike(bench: &mut Bencher) {
    bench.iter(|| {
        let _n = ILike::<true>::ilike(black_box(&b"hello, world!"[..]), black_box(&b"Hello%"[..]));
    })
}

fn bench_bytes_not_ilike(bench: &mut Bencher) {
    bench.iter(|| {
        let _n =
            ILike::<true>::not_ilike(black_box(&b"hello, world!"[..]), black_box(&b"Hello%"[..]));
    })
}

fn bench_str_escape(bench: &mut Bencher) {
    bench.iter(|| {
        let _n = black_box("hello$$_world!").escape(black_box("$"));
    })
}

fn bench_bytes_escape(bench: &mut Bencher) {
    bench.iter(|| {
        let _n = black_box(b"hello$$_world!").escape(black_box(b"$"));
    })
}

benchmark_group!(
    like_benches,
    bench_str_like,
    bench_str_not_like,
    bench_bytes_like,
    bench_bytes_not_like,
    bench_str_ilike,
    bench_str_not_ilike,
    bench_bytes_ilike,
    bench_bytes_not_ilike,
    bench_str_escape,
    bench_bytes_escape,
);
benchmark_main!(like_benches);
