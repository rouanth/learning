import Prelude hiding (Applicative, (<*>), pure, (**), unzip)

{- Laws -}

-- 1) (Tricky) One might imagine a variant of the interchange law that says
-- something about applying a pure function to an effectful argument. Using the
-- above laws, prove that
--
-- pure f <*> x = pure (flip ($)) <*> x <*> pure f

{-
 - (pure (flip ($)) <*> x) <*> pure f
 -
 - By the interchange law:
 - pure ($ f) <*> (pure (flip ($)) <*> x)
 -
 - By the composition law:
 - pure (.) <*> pure ($ f) <*> pure (flip ($)) <*> x
 -
 - By the homomorphism law:
 - pure ((.) ($ f)) <*> pure (flip ($)) <*> x
 -
 - By the homomorphism law:
 - pure ((.) ($ f) (flip ($))) <*> x
 -
 - Now we need to prove that ((.) ($ f) (flip ($))) is indeed f.
 -
 - (.) ($ f) (flip ($))
 -
 -     Recall the definition of (.):
 -     (.) f g = \x -> f (g x)
 -
 - \x -> ($ f) (flip ($) x)
 -
 - Reorder:
 - \x -> ($) (flip ($) x) f
 -
 -     Recall the definition of ($):
 -     ($) h x = h x
 -
 - \x -> flip ($) x f
 -
 -     Recall the definition of `flip`:
 -     flip a b c = a c b
 -
 - \x -> ($) f x
 -
 - \x -> f x
 -
 - Eta reduce:
 - f
 -
 - Thus, 
 - (pure (flip ($)) <*> x) <*> pure f = pure f <*> x
 -}

{- Instances -}

class Functor f => Applicative f where
  pure :: a -> f a
  infixl 4 <*>
  (<*>) :: f (a -> b) -> f a -> f b

newtype ZipList a = ZipList { getZipList :: [a] }
        deriving Show

instance Functor ZipList where
  fmap f (ZipList a) = ZipList $ f <$> a

-- 1) Implement an instance of Applicative for Maybe.

instance Applicative Maybe where
  pure = Just
  (<*>) Nothing  _        = Nothing
  (<*>) (Just f) Nothing  = Nothing
  (<*>) (Just f) (Just a) = Just (f a)

-- 2)  Determine the correct definition of pure for the ZipList instance of
-- Applicative—there is only one implementation that satisfies the law relating
-- pure and (<*>).

instance Applicative ZipList where
  pure x = ZipList (repeat x)
  (ZipList gs) <*> (ZipList xs) = ZipList (zipWith ($) gs xs)

{- Alternative formulation -}

class Functor f => Monoidal f where
  unit :: f ()
  (**) :: f a -> f b -> f (a, b)

-- 1)  Implement pure and (<*>) in terms of unit and (**), and vice versa.

pureMonoidal :: Monoidal f => a -> f a
pureMonoidal a = fmap (const a) unit

starMonoidal :: Monoidal f => f (a -> b) -> f a -> f b
starMonoidal f = fmap (uncurry ($)) . (**) f

unitApplicative :: Applicative f => f ()
unitApplicative = pure ()

combApplicative :: Applicative f => f a -> f b -> f (a, b)
combApplicative a b = (,) <$> a <*> b

-- 2)  Are there any Applicative instances for which there are also functions
-- f () -> () and f (a,b) -> (f a, f b), satisfying some "reasonable" laws? 

{- There are. As long as it's viable to have any function into (), lists are
 - qualified for these functions: -}

unitsToUnit :: [()] -> ()
unitsToUnit _ = ()

unzip :: [(a, b)] -> ([a], [b])
unzip = foldr (\(a, b) (as, bs) -> (a : as, b : bs)) ([], [])

-- 3)  (Tricky) Prove that given your implementations from the first exercise,
-- the usual Applicative laws and the Monoidal laws stated above are
-- equivalent.

{- TODO -}

