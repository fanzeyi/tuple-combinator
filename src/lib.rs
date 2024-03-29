//! A helper trait to improve the ergonomics when working with multiple [`Option`]s. After
//! importing [`TupleCombinator`], you can treat a tuple of `Option`s as one `Option`.
//!
//! # Example
//!
//! ```
//! use tuple_combinator::TupleCombinator;
//!
//! fn main() {
//!     let tuples = (Some(1), Some(2), Some(3));
//!
//!     assert_eq!(tuples.map(|(a,b,c)| a + b + c), Some(6));
//!     assert_eq!(tuples.and_then(|(a,b,c)| Some(a + b - c)), Some(0));
//!     assert_eq!(tuples.transpose(), Some((1,2,3)));
//!     assert_eq!((Some(1), None).map(|(a, b): (i32, i32)| 100), None);
//! }
//! ```

use std::any::Any;

/// The traits that provides helper functions for tuples. This trait implementation mirros most of
/// the methods defined in [`Option`].
#[doc(inline)]
pub trait TupleCombinator: Sized {
    type Tuple;

    /// Transposes a tuple of [`Option`]s into an `Option` of tuples. This function returns `None`
    /// if any of the `Option` is `None`.
    /// ```
    /// # use tuple_combinator::TupleCombinator;
    /// let left = (Some("foo"), Some(123));
    /// assert_eq!(left.transpose(), Some(("foo", 123)));
    /// ```
    fn transpose(self) -> Option<Self::Tuple>;

    /// See [`Option::map`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use tuple_combinator::TupleCombinator;
    /// let tuples = (Some("foo"), Some("bar"));
    /// assert_eq!(tuples.map(|(a, b)| format!("{}{}", a, b)).unwrap(), "foobar");
    /// ```
    fn map<U, F: FnOnce(Self::Tuple) -> U>(self, f: F) -> Option<U> {
        self.transpose().map(f)
    }

    /// See [`Option::expect`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use tuple_combinator::TupleCombinator;
    /// let tuples = (Some("foo"), Some(123));
    /// assert_eq!(tuples.expect("should not panic"), ("foo", 123));
    /// ```
    ///
    /// ```{.should_panic}
    /// # use tuple_combinator::TupleCombinator;
    /// let tuples: (_, Option<i32>) = (Some("foo"), None);
    /// tuples.expect("will panic");
    /// ```
    fn expect(self, msg: &str) -> Self::Tuple {
        self.transpose().expect(msg)
    }

    /// See [`Option::unwrap`].
    /// ```
    /// # use tuple_combinator::TupleCombinator;
    /// let tuples = (Some("foo"), Some(123));
    /// assert_eq!(tuples.unwrap(), ("foo", 123));
    /// ```
    ///
    /// This example will panic:
    ///
    /// ```{.should_panic}
    /// # use tuple_combinator::TupleCombinator;
    /// let tuples: (_, Option<i32>) = (Some("foo"), None);
    /// tuples.unwrap();
    /// ```
    fn unwrap(self) -> Self::Tuple {
        self.transpose().unwrap()
    }

    /// See [`Option::and`].
    /// ```
    /// # use tuple_combinator::TupleCombinator;
    /// let left = (Some("foo"), Some(123));
    /// let right = Some(("bar", 456));
    /// assert_eq!(left.and(right), right);
    ///
    /// let left_none = (None, Some(123));
    /// assert_eq!(left_none.and(right), None);
    /// ```
    fn and(self, optb: Option<Self::Tuple>) -> Option<Self::Tuple> {
        self.transpose().and(optb)
    }

    /// See [`Option::and_then`].
    /// ```
    /// # use tuple_combinator::TupleCombinator;
    /// let tuples = (Some("foobar"), Some(123));
    /// assert_eq!(tuples.and_then(|(a, b)| Some(a.len() + b)), Some(129));
    ///
    /// assert_eq!(tuples.and_then(|(a, b)| if b % 2 != 1 { Some(b) } else { None }), None);
    /// ```
    fn and_then<U, F: FnOnce(Self::Tuple) -> Option<U>>(self, f: F) -> Option<U> {
        self.transpose().and_then(f)
    }

    /// See [`Option::filter`].
    /// ```
    /// # use tuple_combinator::TupleCombinator;
    /// let tuples = (Some("foobar"), Some(123));
    /// assert_eq!(tuples.filter(|(a, b)| b % 2 == 1), Some(("foobar", 123)));
    /// assert_eq!(tuples.filter(|(a, b)| b % 2 != 1), None);
    /// ```
    fn filter<P: FnOnce(&Self::Tuple) -> bool>(self, predicate: P) -> Option<Self::Tuple> {
        self.transpose().filter(predicate)
    }

    /// See [`Option::or`].
    /// ```
    /// # use tuple_combinator::TupleCombinator;
    /// let left = (Some("foo"), Some(123));
    /// let right = Some(("bar", 456));
    /// assert_eq!(left.or(right), left.transpose());
    ///
    /// let left_none = (None, Some(123));
    /// assert_eq!(left_none.or(right), right);
    /// ```
    fn or(self, optb: Option<Self::Tuple>) -> Option<Self::Tuple> {
        self.transpose().or(optb)
    }

    /// See [`Option::or_else`].
    /// ```
    /// # use tuple_combinator::TupleCombinator;
    /// let left = (Some("foo"), Some(123));
    /// let right = Some(("bar", 456));
    /// assert_eq!(left.or_else(|| right), left.transpose());
    /// assert_eq!((None, Some(456)).or_else(|| right), right);
    /// ```
    fn or_else<F: FnOnce() -> Option<Self::Tuple>>(self, f: F) -> Option<Self::Tuple> {
        self.transpose().or_else(f)
    }

    /// See [`Option::xor`].
    /// ```
    /// # use tuple_combinator::TupleCombinator;
    /// let left = (Some("foo"), Some(123));
    /// let right = Some(("bar", 456));
    /// assert_eq!(left.xor(None), left.transpose());
    /// assert_eq!(None.xor(left.transpose()), left.transpose());
    /// assert_eq!(left.xor(right), None);
    /// ```
    fn xor(self, optb: Option<Self::Tuple>) -> Option<Self::Tuple> {
        self.transpose().xor(optb)
    }
}

/// Reduce tuples of [`Option`]s into results of various form, act in comparable to the iterators.
/// ```
/// use tuple_combinator::TupleReducer;
///
/// let res = (Some(1), Some(5), Some("rust_tuple")).fold(0, |sum, item| {
///     sum.and_then(|s| {
///         if let Some(raw_i32) = item.downcast_ref::<Option<i32>>() {
///             return raw_i32.as_ref()
///                 .and_then(|val| {
///                     Some(s + val)
///                 });
///         }
///
///         if let Some(raw_str) = item.downcast_ref::<Option<&str>>() {
///             return raw_str.as_ref()
///                 .and_then(|val| {
///                     Some(s + val.len() as i32)
///                 });
///         }
///
///         Some(s)
///     })
/// });
///
/// assert_eq!(res, Some(16));
/// ```
#[doc(inline)]
pub trait TupleReducer: Sized {
    /// Fold the tuple to obtain a final outcome. Depending on the implementation of the handler
    /// function, the fold can behave differently on various option types or values.
    ///
    /// # Examples
    ///
    /// Reduce tuples of i32 options to the sum of the contained values:
    ///
    /// ```rust
    /// use tuple_combinator::TupleReducer;
    ///
    /// let res = (Some(17), Some(20)).fold(5, |sum, item| {
    ///     sum.and_then(|s| {
    ///         item.downcast_ref::<Option<i32>>()
    ///             .and_then(|raw| raw.as_ref())
    ///             .and_then(|val| {
    ///                 Some(s + val)
    ///              })
    ///     })
    /// });
    ///
    /// assert_eq!(res, Some(42));
    /// ```
    fn fold<U, F: Fn(Option<U>, &dyn Any) -> Option<U>>(&self, init: U, f: F) -> Option<U>;

    /// `fold_strict` works very much like `fold`, except that only options with the same wrapped data
    /// type as the output type will be "folded", i.e. invoking the supplied folding function. This
    /// function will come into handy when the caller only care about the options in the tuples that
    /// match the output type.
    ///
    /// # Examples
    /// ```rust
    /// use tuple_combinator::TupleReducer;
    ///
    /// let res =  (Some(40), Some("noise"), None as Option<i32>, Some(2))
    ///     .fold_strict(0i32, |sum, item| {
    ///         sum.and_then(|s| {
    ///             Some(s + item)
    ///         })
    ///     });
    ///
    /// assert_eq!(res, Some(42));
    /// ```
    fn fold_strict<U: Any, F: Fn(Option<U>, &U) -> Option<U>>(&self, init: U, f: F) -> Option<U>;

    /// Convert the tuples to a reference slice, where caller can use native iteration tools. Note
    /// that this is re-export of the tuples' internal content, hence the slice can't live longer
    /// than the tuple self.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use std::any::Any;
    /// use tuple_combinator::TupleReducer;
    ///
    /// let mut src = (Some(1), None as Option<&str>, Some(2), None as Option<i32>, Some(()));
    ///
    /// // convert the tuples to a slice of `Any` type
    /// let slice: Box<[&dyn Any]> = src.ref_slice();
    ///
    /// // the slice has the same amount of elements as in the tuples.
    /// assert_eq!(slice.len(), 5);
    ///
    /// // downcast the element to its actual type; wrong type cast will be rejected with a `None`
    /// // output from the API call.
    /// assert_eq!(slice[0].downcast_ref::<Option<i32>>().unwrap(), &Some(1));
    /// assert_eq!(slice[0].downcast_ref::<Option<&str>>(), None);
    /// assert_eq!(slice[1].downcast_ref::<Option<&str>>().unwrap(), &None);
    ///
    /// // unlike `mut_slice` API, the line below won't compile even if adding the `mut` keyword
    /// // to the `slice` variable, because the source slice is immutable.
    /// // let first = slice[0].downcast_mut::<Option<i32>>().unwrap().take();
    /// ```
    fn ref_slice(&self) -> Box<[&dyn Any]>;

    /// Convert the tuples to a reference slice which only include options wrapping the data of the
    /// desired type [`T`]. Options with types other than the given one will be excluded from the slice.
    /// Note that if the slice length is 0, it means the source tuple does not contain elements in
    /// options that can be converted to type ['T'].
    ///
    /// # Examples
    /// ```rust
    /// use tuple_combinator::TupleReducer;
    ///
    /// let src = (Some(1), None as Option<&str>, Some(2), None as Option<i32>, Some(()));
    /// let slice = src.strict_ref_slice::<i32>();
    ///
    /// // The above variable initiation is equivalent to the following:
    /// // let slice: Box<[&i32]> = src.strict_ref_slice();
    ///
    /// assert_eq!(slice.len(), 3);
    /// assert_eq!(
    ///     slice,
    ///     vec![&Some(1), &Some(2), &None as &Option<i32>].into_boxed_slice()
    /// );
    ///
    /// // The line below won't compile because the immutability of the slice.
    /// // let first = slice[0].downcast_mut::<Option<i32>>().unwrap().take();
    /// ```
    fn strict_ref_slice<T: Any>(&self) -> Box<[&Option<T>]>;

    /// This method works similar to `ref_slice`, except that the members of the slice are mutable,
    /// such that it is possible to make updates, or taking ownership from the underlying tuples data.
    /// Note that modifying or altering the slice data will also cause the same data in the tuples to
    /// be altered.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use std::any::Any;
    /// use tuple_combinator::TupleReducer;
    ///
    /// let mut src = (Some(1), None as Option<&str>, Some(2), None as Option<i32>, Some(()));
    /// let slice: Box<[&mut dyn Any]> = src.mut_slice();
    ///
    /// assert_eq!(slice.len(), 5);
    /// assert_eq!(slice[0].downcast_ref::<Option<i32>>().unwrap(), &Some(1));
    /// assert_eq!(slice[1].downcast_ref::<Option<&str>>().unwrap(), &None);
    ///
    /// let first = slice[0].downcast_mut::<Option<i32>>().unwrap().take();
    /// assert_eq!(first, Some(1));
    /// ```
    fn mut_slice(&mut self) -> Box<[&mut dyn Any]>;

    /// This method works similar to `strict_ref_slice`, except that the members of the slice are
    /// mutable, such that it is possible to make updates, or taking ownership from the underlying
    /// tuples data. Note that modifying or altering the slice data will also cause the same data
    /// in the tuples to be altered.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use tuple_combinator::TupleReducer;
    ///
    /// let mut src = (Some(1), None as Option<&str>, Some(2), None as Option<i32>, Some(()));
    /// let slice = src.strict_mut_slice::<i32>();
    ///
    /// // The above variable initiation is equivalent to the following:
    /// // let slice: Box<[&mut i32]> = src.strict_mut_slice();
    ///
    /// assert_eq!(slice.len(), 3);
    /// assert_eq!(
    ///     slice,
    ///     vec![&mut Some(1), &mut Some(2), &mut None as &mut Option<i32>].into_boxed_slice()
    /// );
    ///
    /// // Now you can take the wrapped content out of the tuples/slice and operate on the element.
    /// // Note that operations on the slice element will take the same effect on the origin tuples,
    /// // since slice elements are merely mutable borrows.
    /// let first = slice[0].take();
    /// assert_eq!(first, Some(1));
    /// assert_eq!(slice[0], &mut None);
    /// ```
    fn strict_mut_slice<T: Any>(&mut self) -> Box<[&mut Option<T>]>;
}

macro_rules! tuple_impls {
    ( $( $v:ident: $T:ident, )* ) => {
        impl<$($T,)*> TupleCombinator for ($(Option<$T>,)*) {
            type Tuple = ($($T,)*);

            fn transpose(self) -> Option<Self::Tuple> {
                if let ($(Some($v),)*) = self {
                    Some(($($v,)*))
                } else {
                    None
                }
            }
        }

    };
}

macro_rules! tuple_impl_reduce {
    () => {};

    ( $( $ntyp:ident => $nidx:tt, )+ ) => {

        impl<$( $ntyp, )+> TupleReducer for ( $( Option<$ntyp>, )+ )
        where
            $( $ntyp: Any, )*
        {
            fn fold<U, F: Fn(Option<U>, &dyn Any) -> Option<U>>(&self, init: U, f: F) -> Option<U> {
                let mut accu = Some(init);

                $(
                    accu = f(accu, &self.$nidx);
                )*

                accu
            }

            fn fold_strict<U: Any, F: Fn(Option<U>, &U) -> Option<U>>(&self, init: U, f: F) -> Option<U> {
                let mut accu = Some(init);

                $(
                    let opt = (&self.$nidx as &dyn Any)
                        .downcast_ref::<Option<U>>()
                        .and_then(|opt| opt.as_ref());

                    // avoid using combinator here since closure will cause `accu` to move and lead
                    // to all sorts of headache.
                    if let Some(value) = opt {
                        accu = f(accu, value);
                    }
                )*

                accu
            }

            fn ref_slice(&self) -> Box<[&dyn Any]> {
                // The maximum amount of elements in a tuple is 12, that's the upper-bound
                let mut vec: Vec<&dyn Any> = Vec::with_capacity(12);

                $(
                    vec.push(&self.$nidx);
                )*

                vec.into_boxed_slice()
            }

            fn strict_ref_slice<T: Any>(&self) -> Box<[&Option<T>]> {
                // The maximum amount of elements in a tuple is 12, that's the upper-bound
                let mut vec: Vec<&Option<T>> = Vec::with_capacity(12);

                $(
                    (&self.$nidx as &dyn Any)
                        .downcast_ref::<Option<T>>()
                        .and_then(|opt| {
                            vec.push(opt);
                            Some(())
                        });
                )*

                vec.into_boxed_slice()
            }

            fn mut_slice(&mut self) -> Box<[&mut dyn Any]> {
                // The maximum amount of elements in a tuple is 12, that's the upper-bound
                let mut vec: Vec<&mut dyn Any> = Vec::with_capacity(12);

                $(
                    vec.push(&mut self.$nidx);
                )*

                vec.into_boxed_slice()
            }

            fn strict_mut_slice<T: Any>(&mut self) -> Box<[&mut Option<T>]> {
                // The maximum amount of elements in a tuple is 12, that's the upper-bound
                let mut vec: Vec<&mut Option<T>> = Vec::with_capacity(12);

                $(
                    (&mut self.$nidx as &mut dyn Any)
                        .downcast_mut::<Option<T>>()
                        .and_then(|opt| {
                            vec.push(opt);
                            Some(())
                        });
                )*

                vec.into_boxed_slice()
            }
        }
    };
}

// Impl TupleCombinator
tuple_impls! { t1: T1, }
tuple_impls! { t1: T1, t2: T2, }
tuple_impls! { t1: T1, t2: T2, t3: T3, }
tuple_impls! { t1: T1, t2: T2, t3: T3, t4: T4, }
tuple_impls! { t1: T1, t2: T2, t3: T3, t4: T4, t5: T5, }
tuple_impls! { t1: T1, t2: T2, t3: T3, t4: T4, t5: T5, t6: T6, }
tuple_impls! { t1: T1, t2: T2, t3: T3, t4: T4, t5: T5, t6: T6, t7: T7, }
tuple_impls! { t1: T1, t2: T2, t3: T3, t4: T4, t5: T5, t6: T6, t7: T7, t8: T8, }
tuple_impls! { t1: T1, t2: T2, t3: T3, t4: T4, t5: T5, t6: T6, t7: T7, t8: T8, t9: T9, }
tuple_impls! { t1: T1, t2: T2, t3: T3, t4: T4, t5: T5, t6: T6, t7: T7, t8: T8, t9: T9, t10: T10, }

// Impl TupleReducer
tuple_impl_reduce! { T0 => 0, }
tuple_impl_reduce! { T0 => 0, T1 => 1, }
tuple_impl_reduce! { T0 => 0, T1 => 1, T2 => 2, }
tuple_impl_reduce! { T0 => 0, T1 => 1, T2 => 2, T3 => 3, }
tuple_impl_reduce! { T0 => 0, T1 => 1, T2 => 2, T3 => 3, T4 => 4, }
tuple_impl_reduce! { T0 => 0, T1 => 1, T2 => 2, T3 => 3, T4 => 4, T5 => 5, }
tuple_impl_reduce! { T0 => 0, T1 => 1, T2 => 2, T3 => 3, T4 => 4, T5 => 5, T6 => 6, }
tuple_impl_reduce! { T0 => 0, T1 => 1, T2 => 2, T3 => 3, T4 => 4, T5 => 5, T6 => 6, T7 => 7, }
tuple_impl_reduce! { T0 => 0, T1 => 1, T2 => 2, T3 => 3, T4 => 4, T5 => 5, T6 => 6, T7 => 7, T8 => 8, }
tuple_impl_reduce! { T0 => 0, T1 => 1, T2 => 2, T3 => 3, T4 => 4, T5 => 5, T6 => 6, T7 => 7, T8 => 8, T9 => 9, }

#[cfg(test)]
mod impl_tests {
    use super::TupleReducer;
    use std::any::Any;

    #[test]
    fn fold_sum() {
        let res = (Some(17), Some(20)).fold(5, |sum, item| {
            sum.and_then(|s| {
                item.downcast_ref::<Option<i32>>()
                    .and_then(|raw| raw.as_ref())
                    .and_then(|val| Some(s + val))
            })
        });

        assert_eq!(res, Some(42));
    }

    #[test]
    fn fold_mixed() {
        let res = (
            Some(1),
            Some(5),
            Some("rust_tuple"),
            Some(String::from("tuple_reducer")),
            Some(vec![0u8, 1, 42]), // the vec that wraps all the wisdom of this universe
        ).fold(0, |sum, item| {
            sum.and_then(|s| {
                if let Some(raw_i32) = item.downcast_ref::<Option<i32>>() {
                    return raw_i32.as_ref().and_then(|val| Some(s + val));
                }

                if let Some(raw_str) = item.downcast_ref::<Option<&str>>() {
                    return raw_str.as_ref().and_then(|val| Some(s + val.len() as i32));
                }

                if let Some(raw_string) = item.downcast_ref::<Option<String>>() {
                    return raw_string.as_ref().and_then(|val| Some(s + val.len() as i32));
                }

                if let Some(raw_vec) = item.downcast_ref::<Option<Vec<u8>>>() {
                    return raw_vec.as_ref().and_then(|val| Some(s + val.len() as i32));
                }

                Some(s)
            })
        });

        assert_eq!(res, Some(32));
    }

    #[test]
    fn fold_none_as_nuke() {
        let none: Option<i32> = None;

        let res = (Some(1), none, Some(5)).fold(0, |sum, item| {
            sum.and_then(|s| {
                item.downcast_ref::<Option<i32>>()
                    .and_then(|raw| raw.as_ref())
                    .and_then(|val| Some(s + val))
            })
        });

        assert_eq!(res, None);
    }

    #[test]
    fn fold_none_as_reset() {
        let none: Option<i32> = None;
        let init = 0;

        let res = (Some(1), none, Some(5)).fold(init, |sum, item| {
            item.downcast_ref::<Option<i32>>()
                .and_then(|raw| raw.as_ref())
                .and_then(|val| {
                    if let Some(s) = sum {
                        Some(s + val)
                    } else {
                        Some(init + val)
                    }
                })
        });

        assert_eq!(res, Some(5));
    }

    #[test]
    fn fold_strict_base() {
        let res = (Some(40), Some("noise"), None as Option<i32>, Some(2))
            .fold_strict(0i32, |sum, item| {
                sum.and_then(|s| {
                    Some(s + item)
                })
            });

        assert_eq!(res, Some(42));
    }

    #[test]
    fn ref_slice_base() {
        let src = (Some(1), None as Option<&str>, Some(2), None as Option<i32>, Some(()));

         // convert the tuples to a slice of `Any` type
         let slice: Box<[&dyn Any]> = src.ref_slice();

         // the slice has the same amount of elements as in the tuples.
         assert_eq!(slice.len(), 5);

         // downcast the element to its actual type; wrong type cast will be rejected with a `None`
         // output from the API call.
         assert_eq!(slice[0].downcast_ref::<Option<i32>>().unwrap(), &Some(1));
         assert_eq!(slice[0].downcast_ref::<Option<&str>>(), None);
         assert_eq!(slice[1].downcast_ref::<Option<&str>>().unwrap(), &None);
    }

    #[test]
    fn strict_ref_slice_base() {
        let src = (Some(1), None as Option<&str>, Some(2), None as Option<i32>, Some(()));
        let slice = src.strict_ref_slice::<i32>();

        // The above variable initiation is equivalent to the following:
        // let slice: Box<[&i32]> = src.strict_ref_slice();

        assert_eq!(slice.len(), 3);
        assert_eq!(
            slice,
            vec![&Some(1), &Some(2), &None as &Option<i32>].into_boxed_slice()
        );
    }

    #[test]
    fn mut_slice_base() {
        let mut src = (Some(1), None as Option<&str>, Some(2), None as Option<i32>, Some(()));
        let slice: Box<[&mut dyn Any]> = src.mut_slice();

        assert_eq!(slice.len(), 5);
        assert_eq!(slice[0].downcast_ref::<Option<i32>>().unwrap(), &Some(1));
        assert_eq!(slice[1].downcast_ref::<Option<&str>>().unwrap(), &None);

        let first = slice[0].downcast_mut::<Option<i32>>().unwrap().take();
        assert_eq!(first, Some(1));
    }

    #[test]
    fn strict_mut_slice_base() {
        let mut src = (Some(1), None as Option<&str>, Some(2), None as Option<i32>, Some(()));
        let slice = src.strict_mut_slice::<i32>();

        // The above variable initiation is equivalent to the following:
        // let slice: Box<[&mut i32]> = src.strict_mut_slice();

        assert_eq!(slice.len(), 3);
        assert_eq!(
            slice,
            vec![&mut Some(1), &mut Some(2), &mut None as &mut Option<i32>].into_boxed_slice()
        );

        let first = slice[0].take();
        assert_eq!(first, Some(1));
        assert_eq!(slice[0], &mut None);
    }
}
