

length list = case list of
  x:xs -> 1 + length xs
  [] -> 0

-- rep1.png
data U t = U
data K a t = K a
data I t = I t
data (a :+: b) t = Inl a | Inr b
data (a :*: b) t = a :*: b

-- reg.png
class (Functor (PF a)) => Regular a where
  type PF a :: * -> *
  from ::  a -> PF a a
  to :: PF a a -> a

-- rep3.png
data List a = Cons a | Nil

instance Regular (List a) where
  type PF List = (K Int :*: Id) :+: U

  from (Cons x xs) = Inl (K x :*: Id xs)
  from Nil = Inr U

  to (Inl (K x :*: Id xs)) = Cons x xs
  to (Inr U) = Nil

-- gsum.png
class GSum f where
  gsum : f -> Int

instance GSum (K x) where
  gsum (K x) = 0

instance GSum (K Int) where
  gsum (K i) = i

instance (GSum f, GSum g)
         => GSum (f :*: g) where
  gsum (f :*: g) = gsum f + gsum g

instance (GSum f, GSum g)
         => GSum (f :+: g) where
  gsum (Inl f) = gsum f
  gsum (Inr g) = gsum g

instance GSum I where
  gsum (I v) = gsum $ from v

instance GSum U where
  gsum U = 0

-- pgsum

instance GSum (K Int) where
  gsum (K i) = i

instance (GSum f, GSum g)
         => GSum (f :*: g) where
  gsum (f :*: g) = gsum f + gsum g

instance (GSum f, GSum g)
         => GSum (f :+: g) where
  gsum (Inl f) = gsum f
  gsum (Inr g) = gsum g

instance GSum U where
  gsum U = 0
