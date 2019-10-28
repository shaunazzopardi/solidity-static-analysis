{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}

{-TODO

  1. Push in ArraysOrMappings modeled as store
  2. Array length function, declare type
-}

module SMT.SMTLib2 where

  import Control.Monad
  import Text.Parsec
  import Text.Parsec.String
  import Data.Char hiding (DecimalNumber)
  import Data.List
  import Debug.Trace

  import Parseable
  import Solidity.Solidity hiding (Less, LessOrEqual)

  import Data.List

  class VarsOf a where
    varsOf :: a -> [String]


  type VarName = String
-----------------

  instance Parseable VarName where
    display v = v
--------------------------------------------------------------------------------

  data Values = Val String
                | ValRel GenericRelation
                | Var String deriving (Eq, Ord, Show)
-----------------

  instance Parseable Values where
    display (Val b) = b
    display (ValRel b) = display b
    display (Var b) = b
--------------------------------------------------------------------------------
  instance VarsOf Values where
    varsOf (Val b) = []
    varsOf (ValRel b) = varsOf b
    varsOf (Var b) = [b]
--------------------------------------------------------------------------------
  data ConditionalRels =  CBase Values
                        | Equals GenericRelation GenericRelation
                        | And ConditionalRels ConditionalRels
                        | Or ConditionalRels ConditionalRels
                        | Greater NumberRels NumberRels
                        | Less NumberRels NumberRels
                        | GreaterOrEqual NumberRels NumberRels
                        | LessOrEqual NumberRels NumberRels
                        | Not ConditionalRels deriving (Eq, Ord, Show)
---------------

  instance Parseable ConditionalRels where
    display (CBase boolVal) = display boolVal
    display (Equals r rr) = "(= " ++ display r ++ " " ++ (display rr) ++ ")"
    display (And r rr) = "(and " ++ display r ++ " " ++ (display rr) ++ ")"
    display (Or r rr) = "(or " ++ display r ++ " " ++ (display rr) ++ ")"
    display (Greater r rr) = "(> " ++ display r ++ " " ++ (display rr) ++ ")"
    display (Less r rr) = "(< " ++ display r ++ " " ++ (display rr) ++ ")"
    display (GreaterOrEqual r rr) = "(>= " ++ display r ++ " " ++ (display rr) ++ ")"
    display (LessOrEqual r rr) = "(<= " ++ display r ++ " " ++ (display rr) ++ ")"
    display (Not r) = "(not " ++ display r ++ ")"
--------------------------------------------------------------------------------
  instance VarsOf ConditionalRels where
    varsOf (CBase boolVal) = varsOf boolVal
    varsOf (Equals r rr) = (varsOf r) ++ (varsOf rr)
    varsOf (And r rr) = (varsOf r) ++ (varsOf rr)
    varsOf (Or r rr) = (varsOf r) ++ (varsOf rr)
    varsOf (Greater r rr) = (varsOf r) ++ (varsOf rr)
    varsOf (Less r rr) = (varsOf r) ++ (varsOf rr)
    varsOf (GreaterOrEqual r rr) = (varsOf r) ++ (varsOf rr)
    varsOf (LessOrEqual r rr) = (varsOf r) ++ (varsOf rr)
    varsOf (Not r) = (varsOf r)
--------------------------------------------------------------------------------

  data NumberRels = NBase Values
                  | Plus NumberRels NumberRels
                  | Minus NumberRels NumberRels
                  | Multiply NumberRels NumberRels
                  | Div NumberRels NumberRels
                  | Mod NumberRels NumberRels
                  | PowerOf NumberRels NumberRels deriving (Eq, Ord, Show)
---------------

  instance Parseable NumberRels where
    display (NBase numVal) = display numVal
    display (Plus r rr) = "(+ " ++ display r ++ " " ++ (display rr) ++ ")"
    display (Minus r rr) = "(- " ++ display r ++ " " ++ (display rr) ++ ")"
    display (Multiply r rr) = "(* " ++ display r ++ " " ++ (display rr) ++ ")"
    display (Div r rr) = "(div " ++ display r ++ " " ++ (display rr) ++ ")"
    display (Mod r rr) = "(mod " ++ display r ++ " " ++ (display rr) ++ ")"
    display (PowerOf r rr) = "(^ " ++ display r ++ " " ++ (display rr) ++ ")"
--------------------------------------------------------------------------------
  instance VarsOf NumberRels where
    varsOf (NBase numVal) = varsOf numVal
    varsOf (Plus r rr) = (varsOf r) ++ (varsOf rr)
    varsOf (Minus r rr) = (varsOf r) ++ (varsOf rr)
    varsOf (Multiply r rr) = (varsOf r) ++ (varsOf rr)
    varsOf (Div r rr) = (varsOf r) ++ (varsOf rr)
    varsOf (Mod r rr) = (varsOf r) ++ (varsOf rr)
    varsOf (PowerOf r rr) = (varsOf r) ++ (varsOf rr)
--------------------------------------------------------------------------------
  data StringRels  = SBase Values
                  | Concat StringRels StringRels deriving (Eq, Ord, Show)
---------------

  instance Parseable StringRels where
    display (SBase s) = display s
    display (Concat sr srr) = display sr ++ display srr
--------------------------------------------------------------------------------
  instance VarsOf StringRels where
    varsOf (SBase s) = varsOf s
    varsOf (Concat sr srr) = varsOf sr ++ varsOf srr
--------------------------------------------------------------------------------
  data ArrayOrMappingRels = ArrayBase Values
                | Select ArrayOrMappingRels GenericRelation deriving (Eq, Ord, Show)
---------------
  instance Parseable ArrayOrMappingRels where
    display (ArrayBase arrayVal) = display arrayVal
    display (Select arrayRel numberRel) = "(select " ++ display arrayRel ++ " " ++ (display numberRel) ++ ")"
  --------------------------------------------------------------------------------
  instance VarsOf ArrayOrMappingRels where
    varsOf (ArrayBase arrayVal) = varsOf arrayVal
    varsOf (Select arrayRel numberRel) = (varsOf arrayRel) --TODO deal better with arrays
--------------------------------------------------------------------------------
  data StructRels = StructBase Values
            --       | MemberStore StructRels String GenericRelation
                   | MemberSelect StructRels String
                   deriving (Eq, Ord, Show)
---------------
-- TODO would be changes to base type of each member of struct
--  baseTypeOfStruct :: MappingRels -> Type
--  baseTypeOfMap (MappingBase (MappingVar _ t tt)) = tt
--  baseTypeOfMap (MapStore rel _ _) = baseTypeOfMap rel
--  baseTypeOfMap (MapSelect rel _) = baseTypeOfMap rel

--nameOfStructVar :: StructRels -> String
--nameOfStructVar (StructBase (StructVal name)) = name
--nameOfStructVar (MemberStore structrel _ _) = nameOfStructVar structRel
--nameOfStructVar (MemberSelect structRel _) = nameOfStructVar structRel
---------------
  instance Parseable StructRels where
    display (StructBase val) = display val
  --  display (MemberStore rel s genRell) = "(= " ++ display rel ++ "." ++ (display genRel) ++ " " ++ display genRell ++ ")"
    display (MemberSelect rel genRel) = display rel ++ "." ++ (display genRel)
  --------------------------------------------------------------------------------
  instance VarsOf StructRels where
    varsOf (StructBase val) = varsOf val
  --  display (MemberStore rel s genRell) = "(= " ++ display rel ++ "." ++ (display genRel) ++ " " ++ display genRell ++ ")"
    varsOf (MemberSelect rel genRel) = [v ++ "." ++ genRel | v <- (varsOf rel)]
--------------------------------------------------------------------------------
  --the other here is for variables of Uniterpreted type, or enum, or struct
  data GenericRelation = Cond ConditionalRels | Numb NumberRels | ArraysOrMappings ArrayOrMappingRels | Strings StringRels | Structs StructRels | Other String  deriving (Eq, Ord, Show)
---------------

  instance Parseable GenericRelation where
    display (Cond condRel) = display condRel
    display (Numb numRel) = display numRel
    display (ArraysOrMappings arrayRel) = display arrayRel
    display (Strings rel) = display rel
    display (Structs rel) = display rel
--    display (Function s) = display s
  --  display (AnyVar s) = show s
    display (Other s) = s
    --------------------------------------------------------------------------------
  instance VarsOf GenericRelation where
    varsOf (Cond condRel) = varsOf condRel
    varsOf (Numb numRel) = varsOf numRel
    varsOf (ArraysOrMappings arrayRel) = varsOf arrayRel
    varsOf (Strings rel) = varsOf rel
    varsOf (Structs rel) = varsOf rel
--    display (Function s) = display s
  --  display (AnyVar s) = show s
    varsOf (Other s) = [s]
--------------------------------------------------------------------------------
  data AssertRel = Assign GenericRelation GenericRelation | Rel ConditionalRels | TrueAssert | FalseAssert | ERROR deriving (Eq, Ord, Show)
---------------

  instance Parseable AssertRel where
    display (Assign s genRel) ="(= " ++ display s ++ " " ++ display genRel ++ ")"
    display (Rel genRel) = display genRel
    display (TrueAssert) = "(= true true)"
    display (FalseAssert) = "(= false true)"
    display (ERROR) = "ERROR"
    --------------------------------------------------------------------------------
  instance VarsOf AssertRel where
    varsOf (Assign s genRel) = varsOf s ++ varsOf genRel
    varsOf (Rel genRel) = varsOf genRel
    varsOf (TrueAssert) = []
    varsOf (FalseAssert) = []
    varsOf (ERROR) = []
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

  data Type = Intt | Real | Booll | Stringg | BitVector Integer | Fun Type Type | Array Type Type | Address | UserSort String | Uninterpreted String deriving (Eq, Ord, Show)
-------------
  nullValueOfType :: Type -> String
  nullValueOfType Intt = "0"
  nullValueOfType Real = "0"
  nullValueOfType Booll = "false"
  nullValueOfType Stringg = ""
  nullValueOfType (BitVector _) = "#x0"
  nullValueOfType (Array _ t) = nullValueOfType t
  nullValueOfType Address = "address.0"
  nullValueOfType _ = "ERROR"

-------------
  typeOfTypeName :: TypeName -> Type
  typeOfTypeName (TypeNameMapping elementaryTypeName typeName) = Fun (typeOfElType elementaryTypeName) (typeOfTypeName typeName)
  typeOfTypeName (TypeNameElementaryTypeName elementaryTypeName) = typeOfElType elementaryTypeName
  typeOfTypeName (TypeNameElementaryTypeName elementaryTypeName) = typeOfElType elementaryTypeName
  typeOfTypeName (TypeNameArrayTypeName typeName _) = Array Intt (typeOfTypeName typeName)
  typeOfTypeName (TypeNameUserDefinedTypeName (UserDefinedTypeName ids)) = Uninterpreted (intercalate "." (map unIdentifier ids)) --TODO check that this works correctly

  constraintsOfTypeName :: TypeName -> VarName -> [Z3Construct]
  constraintsOfTypeName (TypeNameArrayTypeName _ (Just expr)) name = [] --TODO,  new uint[6] to denote the length of the array is 6
  constraintsOfTypeName _ _ = []

  typeOfElType :: ElementaryTypeName -> Type
  typeOfElType AddressType = BitVector (20*8)
  typeOfElType BoolType = Booll
  typeOfElType StringType = Stringg
  typeOfElType (IntType _) = Intt
  typeOfElType (UintType _) = Intt
  typeOfElType (BytesType Nothing) = BitVector 8
  typeOfElType (BytesType (Just no)) = BitVector (8 * no)
  typeOfElType (ByteType) = BitVector 8
  typeOfElType (FixedType _) = Real
  typeOfElType (UfixedType _) = Real

  constraintsOfElType :: ElementaryTypeName -> VarName -> [Z3Construct]
  constraintsOfElType (IntType Nothing) name = [Z3Assert $ Assert $ Rel (Less (NBase $ Var (display name)) (PowerOf (NBase $ Val $ show 2) (NBase $ Val (show 256))))]
  constraintsOfElType (UintType Nothing) name = [Z3Assert $ Assert $ Rel (Greater (NBase $ Var (display name)) (NBase $ Val $ show 0)), Z3Assert $ Assert $ Rel (Less (NBase $ Var (display name)) (PowerOf (NBase $ Val $ show 2) (NBase $ Val (show 256))))]
  constraintsOfElType (IntType (Just no)) name = [Z3Assert $ Assert $ Rel (Less (NBase $ Var (display name)) (PowerOf (NBase $ Val $ show 2) (NBase $ Val (show no))))]
  constraintsOfElType (UintType (Just no)) name = [Z3Assert $ Assert $ Rel (Greater (NBase $ Var (display name)) (NBase $ Val $ show 0)), Z3Assert $ Assert $ Rel (Less (NBase $ Var (display name)) (PowerOf (NBase $ Val $ show 2) (NBase $ Val $ show no)))]
  constraintsOfElType _ _ = []

-------------

  instance Parseable Type where
    display Intt = "Int"
    display Real = "Real"
    display Booll = "Bool"
    display Stringg = "String"
    display (BitVector no) = "(_ BitVec " ++ show no ++ ")"
    display (Fun t tt) = "(" ++ display t ++ ") " ++ display tt
    display (Array t tt) = "(Array " ++ display t ++ " " ++ display tt ++ ")"
    display (UserSort name) = name
    display (Uninterpreted name) = name
--------------------------------------------------------------------------------

  data VarDeclaration = Dec String Type deriving (Eq, Ord, Show)
-------------

  instance Parseable VarDeclaration where
    --display (Dec s (Fun t tt)) = "(declare-fun " ++ s ++ " " ++ display (Fun t tt) ++ ")"
    display (Dec s (Fun t tt)) = "(declare-const " ++ s ++ " " ++ display (Array t tt) ++ ")"
    display (Dec s (Uninterpreted ss)) = "(declare-const " ++ display s ++ " " ++ ss ++ ")"
    display (Dec s t) = "(declare-const " ++ s ++ " " ++ display t ++ ")"
    --------------------------------------------------------------------------------
  instance VarsOf VarDeclaration where
    varsOf _ = []
--------------------------------------------------------------------------------

  data SortDeclaration = Struct String [(String, Type)] | Enum String [String] | UninterpretedSort String deriving (Eq, Ord, Show)
-------------

  instance Parseable SortDeclaration where
    display (Struct name vars) = "(declare-datatypes () ((" ++ name ++ " (mk-R" ++ (show $ length vars) ++ " " ++ createRecordType vars ++ "))))"
    display (Enum s types) = "(declare-datatypes () ((" ++ s ++ " " ++ (intercalate " " $ map display types) ++ ")))"--"(declare-datatypes () ((S A B C)))"
    display (UninterpretedSort sort) = "(declare-sort " ++ display sort ++ ")"
    --------------------------------------------------------------------------------
  instance VarsOf SortDeclaration where
    varsOf _ = []
-------------

  createRecordType :: [(String, Type)] -> String
  createRecordType [] = ""
  createRecordType ((s,t):vs) = "(" ++ (s) ++ " " ++ display t ++ ") " ++ createRecordType vs
--------------------------------------------------------------------------------

  data Assert = Assert AssertRel deriving (Eq, Ord, Show)
-------------
  instance Parseable Assert where
    display (Assert rel) = "(assert " ++ display rel ++ ")"
  instance VarsOf Assert where
    varsOf (Assert rel) = varsOf rel
--------------------------------------------------------------------------------

  data Z3Construct = Z3Sort SortDeclaration | Z3Dec VarDeclaration | Z3Assert Assert deriving (Eq, Ord, Show)
-------------
  instance Parseable Z3Construct where
    display (Z3Sort s) = display s
    display (Z3Dec d) = display d
    display (Z3Assert a) = display a
-------------
-------------

  falseAssert = Z3Assert $ Assert $ FalseAssert

  negatez3 :: Z3Construct -> Z3Construct
  negatez3 (Z3Assert (Assert (Rel (Not condRel)))) = (Z3Assert (Assert (Rel condRel)))
  negatez3 (Z3Assert (Assert (Rel condRel))) = (Z3Assert (Assert (Rel (Not condRel))))
  negatez3 _ = (Z3Assert (Assert TrueAssert))

  disjunctz3 :: [AssertRel] -> Maybe AssertRel
  disjunctz3 [] = Just TrueAssert
  disjunctz3 [a] = Just a
  disjunctz3 ((Rel a):as) = case disjunctz3 as of
                                Just (Rel cond) -> Just $ Rel $ Or (a) (cond)
                                Just TrueAssert -> Just TrueAssert
                                Just FalseAssert -> Just FalseAssert
                                _ -> Nothing
  disjunctz3 (_:as) = Nothing
