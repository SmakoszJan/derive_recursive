use derive_recursive::Recursive;

trait Count {
    type Output;
    const ZERO: Self::Output;
    /// Sums up all integer values in the data.
    fn count(&self) -> Self::Output;
}

impl<T: Count<Output = i32>> Count for Vec<T> {
    type Output = i32;
    const ZERO: i32 = 0;
    fn count(&self) -> i32 {
        self.iter().map(T::count).sum()
    }
}

impl Count for i32 {
    type Output = i32;
    const ZERO: i32 = 0;
    fn count(&self) -> i32 {
        *self
    }
}

#[derive(Recursive)]
#[recursive(
    impl Count for Self {
        const ZERO: i32 = 0;
        type Output = i32;
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
