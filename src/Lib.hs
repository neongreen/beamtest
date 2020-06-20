{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Lib where

import Control.Lens
import Data.Generics.Product.Typed (HasType, typed)
import Data.Kind
import Data.Text (Text)
import Database.Beam
import Database.Beam.Backend.SQL
import Database.Beam.MySQL
import Database.Beam.Query.Internal
import Database.MySQL.Base (defaultConnectInfo)
import GHC.TypeLits
import Unsafe.Coerce

----------------------------------------------------------------------------
-- DB
----------------------------------------------------------------------------

data MainDb f = MainDb
  {_mainUsers :: f (TableEntity UserT)}
  deriving (Generic, Database be)

mainDb :: DatabaseSettings be MainDb
mainDb = defaultDbSettings

----------------------------------------------------------------------------
-- User
----------------------------------------------------------------------------

data UserT f = User
  { email :: Columnar f Text,
    firstName :: Columnar f Text,
    lastName :: Columnar f Text,
    password :: Columnar f Text,
    disabled :: Columnar (Nullable f) Bool
  }
  deriving (Generic)

type User = UserT Identity

type UserId = PrimaryKey UserT Identity

deriving instance Show User

deriving instance Eq User

instance Beamable UserT

instance Table UserT where
  data PrimaryKey UserT f = UserId (Columnar f Text) deriving (Generic, Beamable)
  primaryKey = UserId . email

----------------------------------------------------------------------------
-- Main
----------------------------------------------------------------------------

{-
sortUsersByFirstName ::
  Q MySQL MainDb s (UserT (QGenExpr QValueContext MySQL s))
sortUsersByFirstName =
  orderBy_
    (\u -> (asc_ (firstName u), desc_ (lastName u)))
    ( all_
        ( ( _mainUsers ::
              MainDb (DatabaseEntity MySQL MainDb) ->
              DatabaseEntity
                MySQL
                MainDb
                (TableEntity UserT)
          )
            mainDb
        )
    )

querySortUsersByFirstName :: SqlSelect MySQL User
querySortUsersByFirstName = select sortUsersByFirstName

main = do
  conn <- connect defaultConnectInfo
  runBeamMySQLDebug putStrLn conn $ do
    users <- runSelectReturningList querySortUsersByFirstName
    mapM_ (liftIO . putStrLn . show) users
-}

----------------------------------------------------------------------------
-- Model
----------------------------------------------------------------------------

data Where table where
  And :: [Where table] -> Where table
  Or :: [Where table] -> Where table
  Is :: (forall be s. table (QExpr be s) -> QExpr be s value) -> Term value -> Where table

data Term a where
  -- Literals
  In :: [Literal a] -> Term a
  NotIn :: [Literal a] -> Term a
  Contains :: [Literal a] -> Term a
  Contained :: [Literal a] -> Term a
  Any :: [Literal a] -> Term a
  Eq :: Literal a -> Term a
  NotEq :: Literal a -> Term a
  GreaterThan :: Literal a -> Term a
  GreaterThanOrEq :: Literal a -> Term a
  LessThan :: Literal a -> Term a
  LessThanOrEq :: Literal a -> Term a
  -- Ints
  Between :: [Int] -> Term Int
  NotBetween :: [Int] -> Term Int
  Overlap :: [Int] -> Term Int
  -- Strings
  Like :: Text -> Term Text
  NotLike :: Text -> Term Text
  ILike :: Text -> Term Text
  NotILike :: Text -> Term Text
  RegExp :: Text -> Term Text
  NotRegExp :: Text -> Term Text
  IRegExp :: Text -> Term Text
  NotIRegExp :: Text -> Term Text
  Col :: Text -> Term Text
  -- Booleans
  Not :: Bool -> Term Bool

class NotNull a mba where
  notNull :: Literal a -> Literal mba

instance NotNull a a where
  notNull = id

instance NotNull (Maybe a) (Maybe a) where
  notNull = id

instance
  {-# OVERLAPPING #-}
  TypeError ('Text "notNull should not be used on Maybe") =>
  NotNull (Maybe a) b
  where
  notNull = error "inaccessible"

instance {-# OVERLAPPABLE #-} NotNull a (Maybe a) where
  notNull = NotNull

data Literal a where
  String :: Text -> Literal Text
  Int :: Int -> Literal Int
  Number :: Double -> Literal Double
  Boolean :: Bool -> Literal Bool
  NotNull :: Literal a -> Literal (Maybe a)
  Null :: Literal (Maybe a)

deriving instance Show (Literal a)

litBoolean :: NotNull Bool mb => Bool -> Literal mb
litBoolean = notNull . Boolean

-- queryPS :: Where User
-- queryPS =
--   And
--     [ Is "email" (Eq (String "artyom@example.com")),
--       Or
--         [ Is "disabled" (Eq (Boolean False)),
--           Is "disabled" (Eq Null)
--         ]
--     ]

queryPS :: Where UserT
queryPS =
  And
    [ Is email (Eq (String "artyom@example.com")),
      Or
        [ Is disabled (Eq (litBoolean False)),
          Is disabled (Eq Null)
        ]
    ]

type family All p xs :: Constraint where
  All p '[] = ()
  All p (x ': xs) = (p x, All p xs)

type VeryGoodBackend be =
  ( BeamSqlBackend be,
    All (HasSqlEqualityCheck be) '[Text, Int, Bool],
    All
      ( HasSqlValueSyntax
          ( Sql92ExpressionValueSyntax
              ( Sql92SelectTableExpressionSyntax
                  ( Sql92SelectSelectTableSyntax
                      (Sql92SelectSyntax (BeamSqlBackendSyntax be))
                  )
              )
          )
      )
      '[Text, Int, Bool]
  )

whereToBeam ::
  forall be table s.
  (VeryGoodBackend be) =>
  Where table ->
  (table (QExpr be s) -> QExpr be s Bool)
whereToBeam p = \item -> case p of
  -- TODO how to do to "pure True" in Beam?
  And xs -> foldr1 (&&.) (map (flip whereToBeam item) xs)
  Or xs -> foldr1 (||.) (map (flip whereToBeam item) xs)
  Is column term -> case term of
    Eq lit -> eqLit (column item) lit
  where
    eqLit :: QExpr be s a -> Literal a -> QExpr be s Bool
    eqLit val = \case
      String x -> val ==. val_ x
      Int x -> val ==. val_ x
      -- Not handling Number, solely so that 'debug' would work. Otherwise
      -- we can handle it just fine.
      -- Number x -> val ==. val_ x
      Boolean x -> val ==. val_ x
      -- Note: the funny thing is that we can only check one level of NotNull:
      -- https://hackage.haskell.org/package/beam-core-0.8.0.0/docs/src/Database.Beam.Query.Ord.html#CanCheckMaybeEquality
      NotNull (String x) -> val ==. just_ (val_ x)
      NotNull (Int x) -> val ==. just_ (val_ x)
      NotNull (Boolean x) -> val ==. just_ (val_ x)
      Null -> isNothing_ val
      other -> error ("whereToBeam: unacceptable literal: " ++ show other)

selectToBeam ::
  forall table be s.
  ( Beamable table,
    VeryGoodBackend be,
    HasType
      (DatabaseEntity be MainDb (TableEntity table))
      (MainDb (DatabaseEntity be MainDb))
  ) =>
  Where table ->
  Q be MainDb s (table (QExpr be s))
selectToBeam p = do
  -- We assume we only have one database, and that all tables in the
  -- database have distinct types. Then we can select the table by the type.
  -- If this is not true, we can write an explicit mapping using a
  -- typeclass.
  item <-
    all_
      ( (mainDb :: MainDb (DatabaseEntity be MainDb))
          ^. typed @(DatabaseEntity be MainDb (TableEntity table))
      )
  guard_ (whereToBeam p item)
  pure item

showQuery :: IO ()
showQuery = dumpSqlSelect (selectToBeam queryPS)
