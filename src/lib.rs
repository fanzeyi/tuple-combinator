#![allow(non_snake_case)]

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

macro_rules! tuple_impls {
    ( $( $name:ident )+ ) => {
        impl<$($name,)+> TupleCombinator for ($(Option<$name>,)+) {
            type Tuple = ($($name,)+);

            fn transpose(self) -> Option<Self::Tuple> {
                if let ($(Some($name),)+) = self {
                    Some(($($name,)+))
                } else {
                    None
                }
            }
        }

    };
}

tuple_impls! { T1 T2 }
tuple_impls! { T1 T2 T3 }
tuple_impls! { T1 T2 T3 T4 }
tuple_impls! { T1 T2 T3 T4 T5 }
tuple_impls! { T1 T2 T3 T4 T5 T6 }
tuple_impls! { T1 T2 T3 T4 T5 T6 T7 }
tuple_impls! { T1 T2 T3 T4 T5 T6 T7 T8 }
tuple_impls! { T1 T2 T3 T4 T5 T6 T7 T8 T9 }
tuple_impls! { T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 }
