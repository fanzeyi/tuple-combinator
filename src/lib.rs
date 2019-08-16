#![allow(non_snake_case)]

pub trait TupleCombinator {
    type Tuple;

    fn map<U, F: FnOnce(Self::Tuple) -> U>(self, f: F) -> Option<U>;

    fn and_then<U, F: FnOnce(Self::Tuple) -> Option<U>>(self, f: F) -> Option<U>;
}

macro_rules! tuple_impls {
    ( $( $name:ident )+ ) => {
        impl<$($name,)+> TupleCombinator for ($(Option<$name>,)+) {
            type Tuple = ($($name,)+);

            fn map<U, F: FnOnce(Self::Tuple) -> U>(self, f: F) -> Option<U> {
                if let ($(Some($name),)+) = self {
                    Some(f(($($name,)+)))
                } else {
                    None
                }
            }

            fn and_then<U, F: FnOnce(Self::Tuple) -> Option<U>>(self, f: F) -> Option<U> {
                if let ($(Some($name),)+) = self {
                    f(($($name,)+))
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

#[cfg(test)]
mod tests {
    use super::TupleCombinator;

    #[test]
    fn test_map() {
        assert_eq!((Some(1), Some(2)).map(|(a, b)| a + b), Some(3));
        assert_eq!(
            (Some(1), Some(2), Some(3)).map(|(a, b, c)| a + b + c),
            Some(1 + 2 + 3)
        );
        assert_eq!(
            (Some(1), Some(2), Some(3), Some(4)).map(|(a, b, c, d)| a + b + c + d),
            Some(1 + 2 + 3 + 4)
        );
    }
}
