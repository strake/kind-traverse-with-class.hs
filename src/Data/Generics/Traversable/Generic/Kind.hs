{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}
module Data.Generics.Traversable.Generic.Kind where

import Control.Applicative
import Data.Generics.Traversable
import Data.Kind
import Data.PolyKinded
import Data.PolyKinded.Atom
import Data.Proxy
import Generics.Kind

class GTraversable' c (a :: LoT κ -> Type) (k :: LoT κ) where
    gtraverse' :: Applicative p => Proxy c -> (∀ b . c b => b -> p b) -> a k -> p (a k)

instance (GTraversable' c a k, GTraversable' c b k) => GTraversable' c (a :+: b) k where
    gtraverse' proxC f (L1 a) = L1 <$> gtraverse' proxC f a
    gtraverse' proxC f (R1 b) = R1 <$> gtraverse' proxC f b

instance (GTraversable' c a k, GTraversable' c b k) => GTraversable' c (a :*: b) k where
    gtraverse' proxC f (a :*: b) = (:*:) <$> gtraverse' proxC f a <*> gtraverse' proxC f b

instance GTraversable' c V1 k where
    gtraverse' _ _ = \ case

instance GTraversable' c U1 k where
    gtraverse' _ _ U1 = pure U1

instance GTraversable' c a k => GTraversable' c (M1 i c' a) k where
    gtraverse' proxC f (M1 a) = M1 <$> gtraverse' proxC f a

instance c (Interpret t k) => GTraversable' c (Field t) k where
    gtraverse' _ f (Field a) = Field <$> f a

instance GTraversable' c a k => GTraversable' c (c' :=>: a) k where
    gtraverse' proxC f (SuchThat a) = SuchThat <$> gtraverse' proxC f a

instance (∀ t . c (f (t :&&: k))) => GTraversable' c (Exists κ f) k where
    gtraverse' _ f (Exists a) = Exists <$> f a

gtraverse'' :: (GenericK a, GTraversable' c (RepK a) k, Applicative p) => Proxy c -> (∀ b . c b => b -> p b) -> Proxy k -> Proxy a -> a :@@: k -> p (a :@@: k)
gtraverse'' proxC f (Proxy :: Proxy k) (proxA :: Proxy a) = onRep proxA proxA (gtraverse' proxC f :: RepK a k -> _ (RepK a k))

onRep :: (Functor f, GenericK a, GenericK b) => Proxy a -> Proxy b -> (RepK a i -> f (RepK b j)) -> a :@@: i -> f (b :@@: j)
onRep proxA proxB f = fmap (toK' proxB) . f . fromK' proxA

fromK' :: GenericK a => Proxy a -> a :@@: k -> RepK a k
fromK' (Proxy :: Proxy a) = fromK @_ @a

toK' :: GenericK a => Proxy a -> RepK a k -> a :@@: k
toK' (Proxy :: Proxy a) = toK @_ @a
