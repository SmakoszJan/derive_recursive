# A single derive macro for all your recursive traits

This proc-macro trait introduces a special `derive` macro called `Recursive` that can be used to auto-generate a recursive implementation of most traits you'll be writing.

## Using `Recursive`

### with structs

Let's look at the following trait:

```rust
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
```

Here, the `count` function should sum up all `i32` values in a piece of data. Suppose we want to implement it for the following struct:

```rust
struct Foo {
    bar: i32,
    zee: Vec<i32>
}
```

First of all, we have to derive `Recursive` for our type (and import the macro):

```rust
use derive_recursive::Recursive;

// ...

#[derive(Recursive)]
struct Foo {
    bar: i32,
    zee: Vec<i32>
}
```

But this alone won't give us anything. In order to actually generate some code, we need to tell the library what traits to implement and how to implement their functions. We do this using the `recursive` helper macro:

```rust
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
    zee: Vec<i32>
}
```

That's a lot of code, but, as you'll see, it's all really simple. First, we specify which trait we want to implement through a standard impl block. Note that it really is a standard impl block, as it also accepts generics the same way. That is, should the trait or the self-type have any generics, you'd write them as though you were actually implementing the trait. The only difference from a standard impl block is the forced usage of `Self`, rather than a path. `Self` here is only a substitute for the type's name, not the generics. Any generics must actually be given. When we're done specifying the trait, we specify what functions we want to implement. We have to write the full signatures of all required (and maybe optional) functions, as `derive_recursive` doesn't know anything about the traits it implements. The signature is written exactly as if it were in an actual impl block. Then, where normally the function's code would be, we put implementation parameters.

Implementation parameters are how we specify what exactly should be done with the function. Here, we used `aggregate` to tell `Recursive` to merge the results of function calls on `Foo`'s fields with the `+` operator. The `aggregate` parameter also accepts `*`, `&`, `|`, `&&`, `||` as operators, `_` as a special `unit` aggregate, that only returns the result of the last recursive call, and a function path for custom aggregation. This works as expected with associated functions (field types). The `aggregate` parameter can also become `{}` denoting a constructor. The call results are then put together into a `Self`-typed return value. If no `aggregate` parameter is given, only the first field in the struct is processed. It's also worth noting, that any parameters of the recursive function are passed on to the next calls.

Ultimately, it all expands into the following

```rust
impl Count for Foo {
    fn count(&self) -> i32 {
        let Self { bar: f0, zee: f1 } = self;
        { <i32 as Count>::count(f0) + <Vec<i32> as Count>::count(f1) }
    }
}
```

Should you want to implement another trait for `Foo` this way, you  need a new `recursive` helper macro. The below example shows a few concepts mentioned above:

```rust
#[derive(Recursive)]
#[recursive(
    impl<C: Count> Count for Self<C> {
        fn count(&self) -> i32 {
            aggregate = +
        }
    }
)]
#[recursive(
    impl<C, T> Bar<T> for Self<C> {
        fn bar(x: C) -> Self {
            aggregate = {}
        }
    } 
)]
struct Foo<C> {
    bar: C,
    zee: Vec<i32>
}
```

This expands into

```rust
impl<C: Count> Count for Foo<C> {
    fn count(&self) -> i32 {
        let Self { bar: f0, zee: f1 } = self;
        { <C as Count>::count(f0) + <Vec<i32> as Count>::count(f1) }
    }
}
impl<C, T> Bar<T> for Foo<C> {
    fn bar(arg0: C) -> Self {
        Self {
            bar: <C as Bar<T>>::bar(arg0),
            zee: <Vec<i32> as Bar<T>>::bar(arg0),
        }
    }
}
```

Fields affected by the implemented function can also be filtered with the `marker` attribute:

```rust
#[derive(Recursive)]
#[recursive(
    impl Bar for Self {
        fn modify(&mut self) {
            aggregate = _,
            marker = only_this
        }
    }
)]
struct Foo {
    a: String,
    b: u32,
    c: Vec<&'static str>
}
```

Then we can mark the right fields with `#[recursive(<marker>)]`:

```rust
struct Foo {
    #[recursive(only_this)]
    a: String,
    b: u32,
    #[recursive(only_this)]
    c: Vec<&'static str>
}
```

This expands into the following:

```rust
impl Bar for Foo {
    fn modify(&mut self) {
        let Self { a: f0, b: f1, c: f2 } = self;
        {
            <String as Bar>::modify(f0);
            <Vec<&'static str> as Bar>::modify(f2)
        }
    }
}
```

If aggregate was not present, the first field found with the right marker would be affected. You can add multiple markers to the same field, of course. It's worth mentioning that if the aggregate is `{}`, the `marker` attribute is invalid. Construction must affect all fields.

Another useful attribute is the `wrap` attribute. This can be given two different values: `Result` and `Option`. If the attribute is present, all recursive function calls are followed by a `?` and the final returned value is wrapped into the respective variant (`Ok` or `Some`).

### with enums

`recursive_derives` can also work with enums. All attributes mentioned above still apply and `marker` along with `aggregate` modify how variants are processed. For interactions (aggregation and filtering) with the enum's variants, we use `variant_aggregate` and `variant_marker`. `variant_aggregate` is only allowed with non-constructive (`attribute` is not `{}`) associated functions, as there is no aggregation possible when the function gets a receiver. The attribute decides how results produced by recursively applying the functions on the variants are aggregated. It accepts any values the `aggregate` attribute accepts, EXCEPT `{}`. `variant_marker` can be used to filter affected variants. It's only allowed on associated functions and REQUIRED on associated constructive functions (`aggregate` is `{}`). It works exactly the same way the `marker` attribute does, except this time, we apply attributes to the variants themselves.

The below example presents deriving traits such as `Default` and `Clone` from the standard library and our own `Size` trait, determining the memory size of the implementor:

```rust
#[derive(Recursive)]
#[recursive(
    impl Default for Self {
        fn default() -> Self {
            aggregate = {},
            variant_marker = default
        }
    }
)]
#[recursive(
    impl Clone for Self {
        fn clone(&self) -> Self {
            aggregate = {}
        }
    }
)]
#[recursive(
    impl Size for Self {
        fn size() -> usize {
            aggregate = +,
            variant_aggregate = max,
        }
    }
)]
enum Foo {
    #[recursive(default)]
    Bar(String, usize),
    Vee {
        a: Zee,
        b: Vec<u8>
    }
}
```

This expands into

```rust
impl Default for Foo {
    fn default() -> Self {
        Self::Bar(<String as Default>::default(), <usize as Default>::default())
    }
}
impl Clone for Foo {
    fn clone(&self) -> Self {
        match self {
            Self::Bar(f0, f1) => {
                Self::Bar(<String as Clone>::clone(f0), <usize as Clone>::clone(f1))
            }
            Self::Vee { a: f0, b: f1 } => {
                Self::Vee {
                    a: <Zee as Clone>::clone(f0),
                    b: <Vec<u8> as Clone>::clone(f1),
                }
            }
        }
    }
}
impl Size for Foo {
    fn size() -> usize {
        max(
            { <String as Size>::size() + <usize as Size>::size() },
            { <Zee as Size>::size() + <Vec<u8> as Size>::size() },
        )
    }
}
```

## Disclaimer

Note, that this library quite fresh, has not been very tested and is limited in some ways (most notably, it has very limited support for unit structs and variants). However, it should be good enough for most use cases. Should you discover a bug or stumble upon an idea on how to improve the library (including things you need, but the library does not provide), feel free to open an issue (and maybe make the change yourself and add a PR, if you have the time). Note that I won't be working on the library a lot, since I have other, more important projects.