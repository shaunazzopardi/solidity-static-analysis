{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}

{-TODO

  1. Push in arrays modeled as store
  2. Array length function, declare type
  3. Handle structs
-}

module SMT.SMTLib2 where

  import Control.Monad
  import Text.Parsec
  import Text.Parsec.String
  import Data.Char hiding (DecimalNumber)
  import Data.List

  import Parseable
  import Solidity.Solidity

  import Data.List

  class VarsOf a where
    varsOf :: a -> [String]


  type VarName = String
-----------------

  instance Parseable VarName where
    display v = v
--------------------------------------------------------------------------------

  data BoolVal = BoolVal String
                | BoolVar String deriving (Eq, Ord, Show)
-----------------
  --data GenericValues = Val String
    --                  | Var String
      --                | ArraySelect ArrayRels GenericRelation
        --              | StructSelect StructRels String
          --            | MapSelect MapRels GenericRelation

-----------------

  instance Parseable BoolVal where
    display (BoolVal b) = b
    display (BoolVar b) = b
--------------------------------------------------------------------------------
  instance VarsOf BoolVal where
    varsOf (BoolVal b) = []
    varsOf (BoolVar b) = [b]
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
  --we should also allow HexVal

  data NumVal = IntVal String
              | RealVal String
              | IntVar String
              | RealVar String deriving (Eq, Ord, Show)
----------------
----------------

  instance Parseable NumVal where
  --  parser = --whitespace *> (SolidityCode <$> parser) <* whitespace <* eof
    display (IntVal i) = i
    display (RealVal d) = d
    display (IntVar v) = v
    display (RealVar v) = v
--------------------------------------------------------------------------------
  instance VarsOf NumVal where
    varsOf (IntVal i) = []
    varsOf (RealVal d) = []
    varsOf (IntVar v) = [v]
    varsOf (RealVar v) = [v]
--------------------------------------------------------------------------------

  data ConditionalRels =  CBase BoolVal
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

  data NumberRels = NBase NumVal
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
  --we should also allow HexVal

  data StringVal = StringVal String
                  | StringVar String deriving (Eq, Ord, Show)
----------------
----------------

  instance Parseable StringVal where
    display (StringVal s) = s
    display (StringVar v) = v
--------------------------------------------------------------------------------
  instance VarsOf StringVal where
    varsOf (StringVal s) = []
    varsOf (StringVar v) = [v]
--------------------------------------------------------------------------------

  data StringRels  = SBase StringVal
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
  data ArrayVal = ArrayVar String deriving (Eq, Ord, Show)
---------------

  instance Parseable ArrayVal where
    display (ArrayVar s) = s
  --  display (SelectArray arrayval numberRel) = "(select " ++ display arrayRel ++ " " ++ (display numberRel) ++ ")"
--------------------------------------------------------------------------------
  instance VarsOf ArrayVal where
    varsOf (ArrayVar s) = [s]
--------------------------------------------------------------------------------

  data ArrayRels = ArrayBase ArrayVal
                | Select ArrayRels GenericRelation deriving (Eq, Ord, Show)
---------------
  instance Parseable ArrayRels where
    display (ArrayBase arrayVal) = display arrayVal
    display (Select arrayRel numberRel) = "(select " ++ display arrayRel ++ " " ++ (display numberRel) ++ ")"
  --------------------------------------------------------------------------------
  instance VarsOf ArrayRels where
    varsOf (ArrayBase arrayVal) = varsOf arrayVal
    varsOf (Select arrayRel numberRel) = (varsOf arrayRel) --TODO deal better with arrays
--------------------------------------------------------------------------------

  data StructVal = StructVar String
                 | StructMemberSelect StructVal String deriving (Eq, Ord, Show)
---------------

  instance Parseable StructVal where
    display (StructVar s) = s
    display (StructMemberSelect struct child) = display struct ++ "." ++ child
  --------------------------------------------------------------------------------
  instance VarsOf StructVal where
    varsOf (StructVar s) = [s]
    varsOf (StructMemberSelect struct child) = [v ++ "." ++ child | v <- (varsOf struct)]
--------------------------------------------------------------------------------

  data StructRels = StructBase StructVal
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

  data MappingVal = MappingVar String Type Type deriving (Eq, Ord, Show)
            --      | SelectMap MappingVal GenericRelation
---------------

  instance Parseable MappingVal where
    display (MappingVar s _ _) = s
--    display (SelectMap s _ _) = "(select " ++ display rel ++ " " ++ (display genRel) ++ ")"
--------------------------------------------------------------------------------
  instance VarsOf MappingVal where
    varsOf (MappingVar s _ _) = [s]
--------------------------------------------------------------------------------

  data MappingRels = MappingBase MappingVal
            --       | MapStore MappingRels GenericRelation GenericRelation
                   | MapSelect MappingRels GenericRelation deriving (Eq, Ord, Show)
---------------

  baseTypeOfMap :: MappingRels -> Type
  baseTypeOfMap (MappingBase (MappingVar _ t tt)) = tt
--  baseTypeOfMap (MapStore rel _ _) = baseTypeOfMap rel
  baseTypeOfMap (MapSelect rel _) = baseTypeOfMap rel
---------------
  instance Parseable MappingRels where
    display (MappingBase val) = display val
  --  display (MapStore rel genRel genRell) = "(store " ++ display rel ++ " " ++ (display genRel) ++ " " ++ display genRell ++ ")"
    display (MapSelect rel genRel) = "(select " ++ display rel ++ " " ++ (display genRel) ++ ")"
    --------------------------------------------------------------------------------
  instance VarsOf MappingRels where
    varsOf (MappingBase val) = varsOf val
    --  display (MapStore rel genRel genRell) = "(store " ++ display rel ++ " " ++ (display genRel) ++ " " ++ display genRell ++ ")"
    varsOf (MapSelect rel genRel) = (varsOf rel)
--------------------------------------------------------------------------------

  --the other here is for variables of Uniterpreted type, or enum, or struct
  data GenericRelation = Cond ConditionalRels | Numb NumberRels | Arrays ArrayRels | Mapping MappingRels | Strings StringRels | Structs StructRels | Other String  deriving (Eq, Ord, Show)
---------------

  instance Parseable GenericRelation where
    display (Cond condRel) = display condRel
    display (Numb numRel) = display numRel
    display (Arrays arrayRel) = display arrayRel
    display (Mapping rel) = display rel
    display (Strings rel) = display rel
    display (Structs rel) = display rel
--    display (Function s) = display s
  --  display (AnyVar s) = show s
    display (Other s) = s
    --------------------------------------------------------------------------------
  instance VarsOf GenericRelation where
    varsOf (Cond condRel) = varsOf condRel
    varsOf (Numb numRel) = varsOf numRel
    varsOf (Arrays arrayRel) = varsOf arrayRel
    varsOf (Mapping rel) = varsOf rel
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
  constraintsOfElType (IntType Nothing) name = [Z3Assert $ Assert $ Rel (Less (NBase $ IntVar (display name)) (PowerOf (NBase $ IntVal $ show 2) (NBase $ IntVal (show 256))))]
  constraintsOfElType (UintType Nothing) name = [Z3Assert $ Assert $ Rel (Greater (NBase $ IntVar (display name)) (NBase $ IntVal $ show 0)), Z3Assert $ Assert $ Rel (Less (NBase $ IntVar (display name)) (PowerOf (NBase $ IntVal $ show 2) (NBase $ IntVal (show 256))))]
  constraintsOfElType (IntType (Just no)) name = [Z3Assert $ Assert $ Rel (Less (NBase $ IntVar (display name)) (PowerOf (NBase $ IntVal $ show 2) (NBase $ IntVal (show no))))]
  constraintsOfElType (UintType (Just no)) name = [Z3Assert $ Assert $ Rel (Greater (NBase $ IntVar (display name)) (NBase $ IntVal $ show 0)), Z3Assert $ Assert $ Rel (Less (NBase $ IntVar (display name)) (PowerOf (NBase $ IntVal $ show 2) (NBase $ IntVal $ show no)))]
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
