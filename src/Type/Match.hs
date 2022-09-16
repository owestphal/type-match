{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
module Type.Match (
  -- * Matching functions
  matchTypeOf, matchType,
  matchTypeOfMaybe, matchTypeMaybe,
  -- * Cases
  inCaseOf, inCaseOf', fallbackCase, fallbackCase',
  Case,
  ) where

import Data.Maybe (fromMaybe)
import Type.Reflection

-- | match against the type of a term
--
-- /raises an error if no cases match/
matchTypeOf :: forall a r. Typeable a => a -> [Case r] -> r
matchTypeOf x cs = fromMaybe (defaultError @a "matchTypeOf") $ matchTypeOfMaybe x cs

-- | same as 'matchTypeOf', but returns 'Nothing' if no cases match.
matchTypeOfMaybe :: forall a r. Typeable a => a -> [Case r] -> Maybe r
matchTypeOfMaybe x = matchTypeOf'
  where
    matchTypeOf' [] = Nothing
    matchTypeOf' (Fallback f:_) = Just $ f x
    matchTypeOf' (ConstFallback r:_) = Just r
    matchTypeOf' (Case ty bdy:cs) =
      case typeOfX `eqTypeRep` ty of
        Just HRefl -> Just $ bdy x
        Nothing -> matchTypeOf' cs
    matchTypeOf' (Const ty r:cs) =
      case typeOfX `eqTypeRep` ty of
        Just HRefl -> Just r
        Nothing -> matchTypeOf' cs
    typeOfX = typeOf x

-- | match against the type itself (usually provided through @TypeApplications@)
--
-- /raises an error if no cases match/
matchType :: forall a r. Typeable a => [Case r] -> r
matchType = matchType' @a "matchType" (defaultError @a "matchType") id

-- | same as 'matchType', but returns 'Nothing' if no cases match.
matchTypeMaybe :: forall a r. Typeable a => [Case r] -> Maybe r
matchTypeMaybe = matchType' @a "matchTypeMaybe" Nothing Just

matchType' :: forall a r b. Typeable a => String -> b -> (r -> b) -> [Case r] -> b
matchType' _ e _ [] = e
matchType' caller _ _ (Fallback{}:_) = error $ caller ++ ": fallbackCase in cases"
matchType' caller _ _ (Case{}:_) = error $ caller ++ ": inCaseOf in cases"
matchType' _ _ f (ConstFallback r:_) = f r
matchType' caller e f (Const ty r:cs) =
  case typeRep @a `eqTypeRep` ty of
    Just HRefl -> f r
    Nothing -> matchType' @a caller e f cs


-- | abstract type for cases
data Case r where
  Case :: TypeRep a -> (a -> r) -> Case r
  Const :: TypeRep a -> r -> Case r
  Fallback :: (forall a. Typeable a => a -> r) -> Case r
  ConstFallback :: r -> Case r

-- | case with access to the scutinee
inCaseOf :: forall a r. Typeable a => (a -> r) -> Case r
inCaseOf = Case typeRep

-- | case with constant result
inCaseOf' :: forall a r. Typeable a => r -> Case r
inCaseOf' = Const (typeRep @a)

-- | fallback case, matches against every type
fallbackCase :: (forall a. Typeable a => a -> r) -> Case r
fallbackCase = Fallback

-- | constant fallback case
fallbackCase' :: r -> Case r
fallbackCase' = ConstFallback

defaultError :: forall a r. Typeable a => String -> r
defaultError caller = error $ caller ++ ": no case for type " ++ show (typeRep @a)

-- example usage
_example :: Typeable a => a -> Int
_example t = matchTypeOf t
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

_someTerm :: Int
_someTerm = 5 + 7

_someOtherTerm :: [String]
_someOtherTerm = ["Hi","how","are","you","?"]
