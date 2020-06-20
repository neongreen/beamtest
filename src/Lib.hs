{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}

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

data Literal a where
  String :: Text -> Literal Text
  Int :: Int -> Literal Int
  Number :: Double -> Literal Double
  Boolean :: Bool -> Literal Bool
  Null :: Literal a

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
        [ Is disabled (Eq (Boolean False)),
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
whereToBeam p item = case p of
  -- TODO how to do to "pure True" in Beam?
  And xs -> foldr1 (&&.) (map (flip whereToBeam item) xs)
  Or xs -> foldr1 (||.) (map (flip whereToBeam item) xs)
  Is column term -> case term of
    Eq lit -> case lit of
      String x -> column item ==. val_ x
      Int x -> column item ==. val_ x
      -- Not handling Number, solely so that 'debug' would work. Otherwise
      -- we can handle it just fine.
      -- Number x -> column item ==. val_ x
      Boolean x -> column item ==. val_ x
      Null -> isNothing_ (column item)

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
