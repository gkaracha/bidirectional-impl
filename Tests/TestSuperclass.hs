data Bool = True | False

data List (a :: *) = Cons a (List a) | Nil

data Nat = Succ Nat | Zero

data Maybe (a:: *) = Just a | Nothing

class () => Eq (a :: *) where {
  eq :: a -> a -> Bool
}

class (Eq a) => Ord (a :: *) where {
  lessOrEqualThan :: a -> a -> Bool
}

class () => Functor (f :: * -> *) where {
  fmap :: forall (a :: *). forall (b :: *). (a -> b) -> f a -> f b
}

instance () => Eq Bool where {
  eq = \a. \b. case a of
                 { True  -> case b of
                              { True  -> True
                              ; False -> False }
                 ; False -> case b of
                              { True  -> False
                              ; False -> True }
                 }
}

instance () => Eq Nat where {
  eq = \a. \b. case a of
                 { Zero  -> case b of
                              { Zero  -> True
                              ; Succ b' -> False }
                 ; Succ a' -> case b of
                              { Zero  -> False
                              ; Succ b' -> eq a' b' }
                 }
}

instance () => Ord Nat where {
  lessOrEqualThan = \a. \b. case eq a b of
                 { True  -> True
                 ; False -> case a of
                              { Zero  -> True
                              ; Succ a' -> case b of
                                             { Zero -> False
                                             ; Succ b' -> lessOrEqualThan a' b'}}}
}

instance (Eq a) => Eq (List (a :: *)) where {
  eq = \a. \b. case a of {
    Nil -> case b of {
      Nil -> True;
      Cons qsdf asdf -> False
    };
    Cons a' as -> case b of {
      Nil -> False;
      Cons b' bs -> case eq a' b' of {
        False -> False;
        True -> eq as bs
      }
    }
  }
}

instance () => Functor List where {
  fmap = \f. \l. case l of {
    Nil -> Nil;
    Cons x xs -> Cons (f x) (fmap f xs)
  }
}

let { lessThan = \a. \b. case lessOrEqualThan a b of {
  False -> False;
  True -> case eq a b of {
    True -> False;
    False -> True
}}} in
\x. \y. lessThan x y
