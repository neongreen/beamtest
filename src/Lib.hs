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

import Control.Lens ((^.))
import Data.Generics.Labels ()
import Data.Generics.Product.Typed (HasType, typed)
import Data.Kind
import Data.String
import Data.Text (Text)
import Data.Void
import Database.Beam
import Database.Beam.Backend.SQL
import Database.Beam.Backend.SQL.Builder
import Database.Beam.MySQL
import Database.Beam.Schema.Tables
import GHC.OverloadedLabels
-- import Database.Beam.Query.Internal
-- import Database.MySQL.Base (defaultConnectInfo)
import GHC.TypeLits

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
-- Labels
----------------------------------------------------------------------------

data Column table value
  = Column (forall be s. VeryGoodBackend be => table (QExpr be s) -> QExpr be s value)

instance value ~ Text => IsLabel "email" (Column UserT value) where
  fromLabel = Column email

instance value ~ Text => IsLabel "first_name" (Column UserT value) where
  fromLabel = Column firstName

instance value ~ Text => IsLabel "last_name" (Column UserT value) where
  fromLabel = Column lastName

instance value ~ Text => IsLabel "password" (Column UserT value) where
  fromLabel = Column password

instance value ~ Maybe Bool => IsLabel "disabled" (Column UserT value) where
  fromLabel = Column disabled

----------------------------------------------------------------------------
-- Cheat
----------------------------------------------------------------------------

instance IsString (Column table value) where
  fromString name = Column (\_ -> QExpr (\_ -> fieldE (unqualifiedField (fromString name))))

----------------------------------------------------------------------------
-- Model
----------------------------------------------------------------------------

type Where = Where' MySQL

data Where' be table where
  And :: [Where' be table] -> Where' be table
  Or :: [Where' be table] -> Where' be table
  Is :: Column table value -> Term be value -> Where' be table

data Term be a where
  -- Literals
  In :: [Literal a] -> Term be a
  NotIn :: [Literal a] -> Term be a
  Contains :: [Literal a] -> Term be a
  Contained :: [Literal a] -> Term be a
  Any :: [Literal a] -> Term be a
  Eq :: HasSqlEqualityCheck be a => Literal a -> Term be a
  NotEq :: HasSqlEqualityCheck be a => Literal a -> Term be a
  GreaterThan :: Literal a -> Term be a
  GreaterThanOrEq :: Literal a -> Term be a
  LessThan :: Literal a -> Term be a
  LessThanOrEq :: Literal a -> Term be a
  -- Ints
  Between :: [Int] -> Term be Int
  NotBetween :: [Int] -> Term be Int
  Overlap :: [Int] -> Term be Int
  -- Strings
  Like :: Text -> Term be Text
  NotLike :: Text -> Term be Text
  ILike :: Text -> Term be Text
  NotILike :: Text -> Term be Text
  RegExp :: Text -> Term be Text
  NotRegExp :: Text -> Term be Text
  IRegExp :: Text -> Term be Text
  NotIRegExp :: Text -> Term be Text
  Col :: Text -> Term be Text
  -- Booleans
  Not :: Bool -> Term be Bool

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
  -- Null :: Literal (Maybe a)
  Null :: Literal (Maybe Void)

deriving instance Show (Literal a)

-- TODO: replace with pattern synonyms?
litBoolean :: NotNull Bool mb => Bool -> Literal mb
litBoolean = notNull . Boolean

instance BeamSqlBackend be => HasSqlEqualityCheck be Void

-- queryPS :: Where User
-- queryPS =
--   And
--     [ Is "email" (Eq (String "artyom@example.com")),
--       Or
--         [ Is "disabled" (Eq (Boolean False)),
--           Is "disabled" (Eq Null)
--         ]
--     ]

-- Can just use 'Where' in production
queryPS :: VeryGoodBackend be => Where' be UserT
queryPS =
  And
    [ Is "email" (Eq (String "artyom@example.com")),
      Or
        [ Is "disabled" (Eq (Boolean False)),
          Is "disabled" (Eq Null)
        ]
    ]

type family All p xs :: Constraint where
  All p '[] = ()
  All p (x ': xs) = (p x, All p xs)

type VeryGoodBackend be =
  ( BeamSqlBackend be,
    All (HasSqlEqualityCheck be) '[Text, Int, Bool, Double],
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
      '[Text, Int, Bool, Double],
    BeamSqlBackendIsString be Text
  )

whereToBeam ::
  forall be table s.
  (VeryGoodBackend be) =>
  Where' be table ->
  (table (QExpr be s) -> QExpr be s SqlBool)
whereToBeam p = \item -> case p of
  -- TODO how to do to "pure True" in Beam?
  And xs -> foldr1 (&&?.) (map (flip whereToBeam item) xs)
  Or xs -> foldr1 (||?.) (map (flip whereToBeam item) xs)
  Is (Column column) term -> case term of
    In lits -> sqlBool_ (column item `in_` map fromLiteral lits)
    NotIn lits -> sqlBool_ (not_ (column item `in_` map fromLiteral lits))
    -- Contains :: [Literal a] -> Term be a -- not used
    -- Contained :: [Literal a] -> Term be a -- not used
    -- Any :: [Literal a] -> Term be a -- not used
    Eq lit -> column item ==?. fromLiteral lit
    NotEq lit -> column item /=?. fromLiteral lit
    GreaterThan lit -> sqlBool_ (column item >. fromLiteral lit)
    GreaterThanOrEq lit -> sqlBool_ (column item >=. fromLiteral lit)
    LessThan lit -> sqlBool_ (column item <. fromLiteral lit)
    LessThanOrEq lit -> sqlBool_ (column item <=. fromLiteral lit)
    --Between :: [Int] -> Term be Int -- not used
    --NotBetween :: [Int] -> Term be Int -- not used
    --Overlap :: [Int] -> Term be Int -- not used
    Like s -> sqlBool_ (column item `like_` val_ s)
    NotLike s -> sqlBool_ (not_ (column item `like_` val_ s))
    --ILike :: Text -> Term be Text -- not used
    --NotILike :: Text -> Term be Text -- not used
    --RegExp :: Text -> Term be Text -- not used
    --NotRegExp :: Text -> Term be Text -- not used
    --IRegExp :: Text -> Term be Text -- not used
    --NotIRegExp :: Text -> Term be Text -- not used
    --Col :: Text -> Term be Text -- not used

    -- Seems useless
    Not b -> sqlBool_ (not_ (val_ b))
    _ -> undefined

fromLiteral :: VeryGoodBackend be => Literal a -> QExpr be s a
fromLiteral lit = case lit of
  String x -> val_ x
  Int x -> val_ x
  Number x -> val_ x
  Boolean x -> val_ x
  -- Note: the funny thing is that we can only check one level of NotNull:
  -- https://hackage.haskell.org/package/beam-core-0.8.0.0/docs/src/Database.Beam.Query.Ord.html#CanCheckMaybeEquality
  NotNull (String x) -> just_ (val_ x)
  NotNull (Int x) -> just_ (val_ x)
  NotNull (Number x) -> just_ (val_ x)
  NotNull (Boolean x) -> just_ (val_ x)
  NotNull Null -> error ("fromLiteral: unacceptable literal: " ++ show lit)
  NotNull (NotNull _) -> error ("fromLiteral: unacceptable literal: " ++ show lit)
  Null -> nothing_

selectToBeam ::
  forall table be s.
  ( Beamable table,
    VeryGoodBackend be,
    HasType
      (DatabaseEntity be MainDb (TableEntity table))
      (MainDb (DatabaseEntity be MainDb))
  ) =>
  Where' be table ->
  Q be MainDb s (table (QExpr be s))
selectToBeam p =
  -- We assume we only have one database, and that all tables in the
  -- database have distinct types. Then we can select the table by the type.
  -- If this is not true, we can write an explicit mapping using a
  -- typeclass.
  filter_'
    (whereToBeam p)
    ( all_
        ( (mainDb :: MainDb (DatabaseEntity be MainDb))
            ^. typed @(DatabaseEntity be MainDb (TableEntity table))
        )
    )

-- TODO: compare generated queries with Sequelize

showQuery :: IO ()
showQuery = dumpSqlSelect (selectToBeam queryPS)

-- bogus, used only for showQuery
instance HasSqlValueSyntax SqlSyntaxBuilder Double where
  sqlValueSyntax = undefined

----------------------------------------------------------------------------
-- Updates
----------------------------------------------------------------------------

-- Note: we have to be able to get column names and values from a list of
-- assignments, because we want to be able to write them to Redis. We assume
-- that we'll only use MySQL and Redis.

data Assignment be table
  = forall value.
    ( HasSqlValueSyntax
        ( Sql92ExpressionValueSyntax
            ( Sql92SelectTableExpressionSyntax
                ( Sql92SelectSelectTableSyntax
                    (Sql92SelectSyntax (BeamSqlBackendSyntax be))
                )
            )
        )
        value
    ) =>
    Assignment
      (forall f. table (Columnar' f) -> Columnar' f value)
      value

(=:) ::
  ( HasSqlValueSyntax
      ( Sql92ExpressionValueSyntax
          ( Sql92SelectTableExpressionSyntax
              ( Sql92SelectSelectTableSyntax
                  (Sql92SelectSyntax (BeamSqlBackendSyntax be))
              )
          )
      )
      value
  ) =>
  (forall f. table (Columnar' f) -> Columnar' f value) ->
  value ->
  [Assignment be table]
(=:) a b = [Assignment a b]

updatePS :: [Assignment MySQL UserT]
updatePS =
  email =: "artyom@monadfix.com"
    <> disabled =: Just False

columnize :: Beamable table => table f -> table (Columnar' f)
columnize = changeBeamRep Columnar'

fromColumnar' :: Columnar' f value -> Columnar f value
fromColumnar' (Columnar' x) = x

assignmentsToBeam ::
  forall be table s.
  (Beamable table, VeryGoodBackend be) =>
  [Assignment be table] ->
  (table (QField s) -> QAssignment be s)
assignmentsToBeam assignments = \item ->
  let item' :: table (Columnar' (QField s))
      item' = columnize item
   in mconcat $
        map
          ( \(Assignment column (value :: value)) ->
              fromColumnar' (column item') <-. val_ value
          )
          assignments

-- > map getAssignmentColumn updatePS
-- ["email","disabled"]
getAssignmentColumn ::
  forall be table.
  ( Beamable table,
    HasType
      (DatabaseEntity be MainDb (TableEntity table))
      (MainDb (DatabaseEntity be MainDb))
  ) =>
  Assignment be table ->
  Text
getAssignmentColumn (Assignment column _) =
  let entity :: DatabaseEntity be MainDb (TableEntity table) =
        (mainDb :: MainDb (DatabaseEntity be MainDb))
          ^. typed @(DatabaseEntity be MainDb (TableEntity table))
      DatabaseEntity dt@(DatabaseTable {}) = entity
   in fromColumnar' (column (columnize (dbTableSettings dt))) ^. fieldName
