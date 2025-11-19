# Multi-Verifier Keyed-Verification Anonymous Credentials Implementation


# Benchmark
To run the benchmarks, it is better to build the project with "release" tag:

```shell
cargo build --release
```

Then, you can run the benchmark with the following command:

```shell
BENCH_ROUNDS=1000 BENCH_ATTRS=4,6,8,10,12 cargo run --release --bin benchmark
```

# Team 
* [Jan Bobolz](https://jan-bobolz.de/)
* [Emad Heydari Beni](https://heydari.be)
* [Anja Lehmann](https://hpi.de/lehmann/team/anja-lehmann.html)
* [Omid Mirzamohammadi](https://www.esat.kuleuven.be/cosic/people/person/?u=u0159898)
* [Cavit Özbay](https://hpi.de/lehmann/team/cavit-oezbay.html)
* [Mahdi Sedaghat](https://mahdi171.github.io/)
