import Prelude hiding (Functor, fmap)

{-  Instances --}

class Functor f where
  fmap :: (a -> b) -> f a -> f b

instance Functor [] where
  fmap f [] = []
  fmap f (a : as) = f a : fmap f as

instance Functor Maybe where
  fmap _ Nothing  = Nothing
  fmap f (Just a) = Just $ f a

-- 1) Implement Functor instances for Either e and ((->) e).

instance Functor (Either e) where
  fmap f (Left  a) = Left a
  fmap f (Right a) = Right (f a)

instance Functor ((->) e) where
  fmap = (.)

-- 2) Implement Functor instances for ((,) e) and for Pair, defined as

data Pair a = Pair a a

--    Explain their similarities and differences. 

instance Functor ((,) e) where
  fmap f (e, a) = (e, f a)

instance Functor Pair where
  fmap f (Pair a b) = Pair (f a) (f b)

   {- In the first case, the first element of a pair is the context and so
      isnt changed; in the second one, however, both elements are values
      contained in the functor, so we need to modify the first one as well. -}

-- 3) Implement a Functor instance for the type ITree, defined as

data ITree a = Leaf (Int -> a) | Node [ITree a]

instance Functor ITree where
  fmap f (Leaf g) = Leaf $ fmap f g
  fmap f (Node k) = Node $ fmap (fmap f) k

-- 4) Give an example of a type of kind * -> * which cannot be made an instance
--    of Functor (without using undefined).

data NotAFunctor a = NotAFunctor (a -> ())

-- 5) Is this statement true or false?
--
--     The composition of two Functors is also a Functor.
--
--    If false, give a counterexample; if true, prove it by exhibiting some
--    appropriate Haskell code.

data Compose f g x = Compose (f (g x))

instance (Functor f, Functor k) => Functor (Compose f k) where
  fmap f (Compose n) = Compose $ fmap (fmap f) n

{- Laws -}

-- 1) Although it is not possible for a Functor instance to satisfy the first
--    Functor law but not the second (excluding undefined), the reverse is
--    possible. Give an example of a (bogus) Functor instance which satisfies
--    the second law but not the first.

data WrongFunctor a = WrongFunctor Int a

instance Functor WrongFunctor where
  fmap f (WrongFunctor i a) = WrongFunctor 0 (f a)

  {- The second law holds:
     fmap (f . g) (WrongFunctor i a) = WrongFunctor 0 (f (g a)) =
     fmap f $ WrongFunctor i (g a) = fmap f $ fmap g $ WrongFunctor i a

     and, by reduction,
     fmap (f . g) = fmap f . fmap g

     WrongFunctor i a = id $ WrongFunctor i a = fmap id (WrongFunctor 0 a) =
     id $ WrongFunctor 0 a = WrongFunctor 0 a <=>
     WrongFunctor i a = WrongFunctor 0 a      <=>
     i = 0

     The first law holds only for i = 0. -}

-- 2)
--
-- instance Functor [] where
--   fmap _ [] = []
--   fmap g (x:xs) = g x : g x : fmap g xs
--
--    Which laws are violated by the evil Functor instance for list shown
--    above: both laws, or the first law alone? Give specific counterexamples.

-- Evil Functor instance

  {- Violation of the first law: `fmap id [1] == [1, 1]`, but `id [1] == [1]`.
     Violation of the second law: `fmap (id . id) [1] == [1, 1]`, but
       `(fmap id) . (fmap id) $ [1] == fmap id $ [1, 1] == [1, 1, 1, 1] -}

