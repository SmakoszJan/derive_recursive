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

trait Bar<T> {
    fn bar(self) -> Self;
}

impl<T> Bar<T> for i32 {
    fn bar(self) -> Self {
        self
    }
}

impl<T, U> Bar<T> for Vec<U> {
    fn bar(self) -> Self {
        self
    }
}

#[derive(Clone, Debug, PartialEq)]
#[derive(Recursive)]
#[recursive(
    impl<C: Count> Count for Self<C> {
        fn count(&self) -> i32 {
            aggregate = +
        }
    }
)]
#[recursive(
    impl<C: Bar<T>, T> Bar<T> for Self<C> {
        fn bar(self) -> Self {
            aggregate = {}
        }
    } 
)]
struct Foo<C> {
    bar: C,
    zee: Vec<i32>
}
fn main() {
    let foo = Foo {
        bar: 1,
        zee: vec![2, 3],
    };
    assert_eq!(foo.count(), 6);
    assert_eq!(foo, <Foo<i32> as Bar<u8>>::bar(foo.clone()));
}
