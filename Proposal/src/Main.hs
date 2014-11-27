{-# Language TemplateHaskell, TypeFamilies, FlexibleInstances, FlexibleContexts, TypeOperators #-}
import qualified Generics.Regular as R
import Data.Typeable

data List a = Cons a (List a) | Nil deriving Show

$(R.deriveAll ''List "GListR") 

type instance R.PF (List a) = GListR a

class GMap f where
  gmap' :: (GMap (R.PF r), R.Regular r) =>  (Int -> Int) -> f r -> f r

instance GMap (R.U) where
  gmap' _ _ = R.U

instance Typeable a => GMap (R.K a) where
  gmap' f (R.K v) =
    case cast v of
      Just i -> R.K $ (\(Just x) -> x) $ cast $ f i
      Nothing -> R.K v

instance GMap R.I where
  gmap' f (R.I r) = R.I $ R.to $ gmap' f $ R.from r

instance (GMap f, GMap g) => GMap (f R.:+: g) where
  gmap' f (R.L g) = R.L $ gmap' f g
  gmap' f (R.R g) = R.R $ gmap' f g

instance (GMap f, GMap g) => GMap (f R.:*: g) where 
  gmap' f (g R.:*: h) = gmap' f g R.:*: gmap' f h

instance GMap g => GMap (R.C c g) where
  gmap' f (R.C g) = R.C $ gmap' f g

gmap f = R.to . gmap' f . R.from

asum = gmap (+1) (Cons (1 :: Int) Nil)
