use derive_recursive::Recursive;

trait Count {
    /// Sums up all integer values in the data.
    fn count(&self) -> i32;
}

impl<T: Count> Count for Vec<T> {
    fn count(&self) -> i32 {
        self.iter().map(T::count).sum()
    }
}

impl Count for i32 {
    fn count(&self) -> i32 {
        *self
    }
}

#[derive(Recursive)]
#[recursive(
    impl Count for Self {
        fn count(&self) -> i32 {
            aggregate = +
        }
    }
)]
struct Foo {
    bar: i32,
    zee: Vec<i32>,
}

fn main() {
    let foo = Foo {
        bar: 1,
        zee: vec![2, 3],
    };
    assert_eq!(foo.count(), 6);
}
