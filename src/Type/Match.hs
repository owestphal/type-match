{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PolyKinds #-}
module Type.Match (
  -- * Matching functions
  matchTypeOf, matchType,
  matchTypeOfMaybe, matchTypeMaybe,
  -- * Cases
  inCaseOf, inCaseOf',
  fallbackCase, fallbackCase',
  inCaseOfE, inCaseOfE',
  Case,
  ) where

import Data.Maybe (fromMaybe)
import Type.Reflection

-- | match against the type of a term
--
-- /raises an error if no cases match/
matchTypeOf :: forall a r. Typeable a => a -> [Case a r] -> r
matchTypeOf x cs = fromMaybe (defaultError @a "matchTypeOf") $ matchTypeOfMaybe x cs

-- | same as 'matchTypeOf', but returns 'Nothing' if no cases match.
matchTypeOfMaybe :: forall a r. Typeable a => a -> [Case a r] -> Maybe r
matchTypeOfMaybe x = matchTypeOf'
  where
    matchTypeOf' [] = Nothing
    matchTypeOf' (Fallback f:_) = Just $ f x
    matchTypeOf' (ConstFallback r:_) = Just r
    matchTypeOf' (Case ty bdy:cs) =
      case typeOfA `eqTypeRep` ty of
        Just HRefl -> Just (bdy HRefl x)
        Nothing -> matchTypeOf' cs
    matchTypeOf' (Const ty r:cs) =
      case typeOfA `eqTypeRep` ty of
        Just HRefl -> Just (r HRefl)
        Nothing -> matchTypeOf' cs
    matchTypeOf' (AppCase ty bdy : cs) =
      case typeOfA of
        App f _ -> case f `eqTypeRep` ty of
          Just HRefl -> Just (bdy HRefl x)
          Nothing -> matchTypeOf' cs
        _ -> matchTypeOf' cs
    matchTypeOf' (AppCaseConst ty r : cs) =
      case typeOfA of
        App f _ -> case f `eqTypeRep` ty of
          Just HRefl -> Just (r HRefl)
          Nothing -> matchTypeOf' cs
        _ -> matchTypeOf' cs
    typeOfA :: TypeRep a
    typeOfA = typeOf x

-- | match against the type itself (usually provided through @TypeApplications@)
--
-- /raises an error if no cases match/
matchType :: forall {k} (a :: k) r. Typeable a => [Case a r] -> r
matchType = matchType' @a "matchType" (defaultError @a "matchType") id

-- | same as 'matchType', but returns 'Nothing' if no cases match.
matchTypeMaybe :: forall {k} (a :: k) r. Typeable a => [Case a r] -> Maybe r
matchTypeMaybe = matchType' @a "matchTypeMaybe" Nothing Just

matchType' :: forall {k} (a :: k) r b. Typeable a => String -> b -> (r -> b) -> [Case a r] -> b
matchType' _ e _ [] = e
matchType' caller _ _ (Fallback{}:_) = error $ caller ++ ": fallbackCase in cases (only constant cases are allowed here)"
matchType' caller _ _ (Case{}:_)     = error $ caller ++ ": inCaseOf in cases (only constant cases are allowed here)"
matchType' caller _ _ (AppCase{}:_)  = error $ caller ++ ": inCaseOfApp in cases (only constant cases are allowed here)"
matchType' _ _ f (ConstFallback r:_) = f r
matchType' caller e f (Const ty r:cs) =
  case typeRep @a `eqTypeRep` ty of
    Just HRefl -> f (r HRefl)
    Nothing -> matchType' @a caller e f cs
matchType' caller e f (AppCaseConst ty r:cs) =
  case typeRep @a of
    App con _ -> case con `eqTypeRep` ty of
      Just HRefl -> f (r HRefl)
      Nothing -> matchType' caller e f cs
    _ -> matchType' caller e f cs

-- | abstract type for cases
data Case (x :: k) r where
  Case :: TypeRep a -> (a :~~: x -> a -> r) -> Case x r
  Const :: TypeRep a -> (a :~~: x -> r) -> Case x r
  AppCase :: TypeRep f -> (forall a. f a :~~: x -> f a -> r) -> Case x r
  AppCaseConst :: TypeRep f -> (forall a. f a :~~: x -> r) -> Case x r
  Fallback :: (forall a. Typeable a => a -> r) -> Case x r
  ConstFallback :: r -> Case x r

-- | case with access to the scrutinee
inCaseOf :: forall a x r. Typeable a => (a -> r) -> Case x r
inCaseOf f = Case typeRep (const f)

-- | case with constant result
inCaseOf' :: forall a x r. Typeable a => r -> Case x r
inCaseOf' = Const (typeRep @a) . const

-- | same as 'inCaseOf' but with access to the underlying equality
inCaseOfE :: forall a x r. Typeable a => (a :~~: x -> a -> r) -> Case x r
inCaseOfE = Case typeRep

-- | same as 'inCaseOf'' but with access to the underlying equality
inCaseOfE' :: forall a x r. Typeable a => (a :~~: x -> r) -> Case x r
inCaseOfE' = Const typeRep

-- | case matching against a types outer constructor
inCaseOfApp :: Typeable f => (forall a. f a :~~: x -> f a  -> r) -> Case x r
inCaseOfApp = AppCase typeRep

-- | case matching against a types outer constructor with constant result
inCaseOfApp' :: forall f x r. Typeable f => (forall a. f a :~~: x -> r) -> Case x r
inCaseOfApp' = AppCaseConst typeRep

-- | fallback case, matches against every type
fallbackCase :: (forall a. Typeable a => a -> r) -> Case x r
fallbackCase = Fallback

-- | constant fallback case
fallbackCase' :: r -> Case x r
fallbackCase' = ConstFallback

defaultError :: forall a r. Typeable a => String -> r
defaultError caller = error $ caller ++ ": no case for type " ++ show (typeRep @a)

-- example usage
_example1 :: Typeable a => a -> Int
_example1 t = matchTypeOf t
  [ inCaseOf @Int id
  , inCaseOf @String length
  , fallbackCase $ \x -> error $ "expected argument type Int or String, but got " ++ show (typeOf x)
  ]

_example2 :: forall a. Typeable a => Maybe String
_example2 = matchType @a
  [ inCaseOf' @Int Nothing
  , inCaseOf' @Bool $ Just "Hi"
  , inCaseOf' @() $ Just "Bye"
  , inCaseOf @String $ Just
  , fallbackCase' $ Just "Good Day"
  ]

data T where
  A :: Typeable a => a -> T

_example3 :: forall a. Typeable a => T -> Maybe a
_example3 (A (x :: b)) = matchType @a
  [ inCaseOfE' @b $ \HRefl -> Just x
  , fallbackCase' Nothing
  ]

_example4 :: forall a. (Show a, Typeable a) => a -> String
_example4 a = matchTypeOf a
  [ inCaseOfApp @[] $ \HRefl x -> unwords ["List with", show (length x),"elements"]
  , inCaseOfApp @Maybe $ \HRefl -> show
  , fallbackCase' "something else"
  ]

_someTerm :: Int
_someTerm = 5 + 7

_someOtherTerm :: [String]
_someOtherTerm = ["Hi","how","are","you","?"]
