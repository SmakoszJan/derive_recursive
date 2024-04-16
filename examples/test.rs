use derive_recursive::Recursive;

#[derive(Recursive)]
#[recursive(
    impl SizeOf for Self {
        fn size_of() -> usize {
            aggregate = +,
            init = 1
        }
    }
)]
struct X {
    v: u32
}