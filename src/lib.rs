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

    /// Convert the tuples to an owned slice, where you can use native iteration tools. Note that
    /// this is re-export of the tuples' internal content, hence the slice can't live longer than
    /// the tuple itself.
    fn to_slice(&self) -> Box<[&dyn Any]>;
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

            fn to_slice(&self) -> Box<[&dyn Any]> {
                // The maximum amount of elements in a tuple is 12, that's the upper-bound
                let mut vec: Vec<&dyn Any> = Vec::with_capacity(12);

                $(
                    vec.push(&self.$nidx);
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
            Some(vec![0u8, 1, 42]), // the vec contains all the knowledge required for the universe to exist
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
    fn to_slice_base() {
        let sli: Box<[&dyn Any]> = (Some(1), None as Option<&str>, Some(2), Some(())).to_slice();

        assert_eq!(sli.len(), 4);
        assert_eq!(sli[0].downcast_ref::<Option<i32>>().unwrap(), &Some(1));
    }

    #[test]
    fn to_slice_closures() {
        let sum = 0;
        let c1 = Some(|| { sum += 1; });
        let c2 = Some(|| { sum += 1; });

        let vec: Vec<&dyn Any> = (c1, c2).to_slice();

        assert_eq!(vec.len(), 2);
        assert_eq!(vec[0].downcast_ref::<Option<i32>>().unwrap(), &Some(1));
    }
}

/* Crazy stuff

#![allow(unused)]

use std::ptr;

trait FnBox {
    fn call_box(&mut self, val: &mut Context);
}

impl<F: Fn(&mut Context) + ?Sized> FnBox for F {
    fn call_box(&mut self, val: &mut Context) {
        self(val);
    }
}

struct Context {
    val: usize,
}

impl Context {
    fn add(&mut self, additional: usize) {
        self.val += additional;
    }
}

fn main() {
    // >>> Struct Updates <<<
    type Func = dyn Fn(&mut Context);

    let mut ctx = Context { val: 0 };
    let c1: Box<Func> = Box::new(|sum: &mut Context| { sum.add(40); }); // if define type as: Box<dyn FnBox>, it also works
    let c2: Box<Func> = Box::new(|sum: &mut Context| { sum.add(2); });

    let mut vec: Vec<Box<Func>> = Vec::new();
    vec.push(c1);
    vec.push(c2);

    vec.iter_mut().for_each(|cl: &mut Box<Func>| {
       cl(&mut ctx);
    });

    // >>> Primitive Updates <<<
    type Func1 = dyn Fn(&mut i32);

    let mut sum = 0;
    let c3: Box<Func1> = Box::new(|sum: &mut i32| { *sum += 40; }); // if define type as: Box<dyn FnBox>, it also works
    let c4: Box<Func1> = Box::new(|sum: &mut i32| { *sum += 2; });

    let mut vec1: Vec<Box<Func1>> = Vec::new();
    vec1.push(c1);
    vec1.push(c2);

    vec1.iter_mut().for_each(|cl: &mut Box<Func1>| {
        cl(&mut sum);
    });

    println!("sum: {}", &sum.val);
}

*/
