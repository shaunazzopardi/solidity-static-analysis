{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}

{-TODO

  1. Push in arrays modeled as store
  2. Array length function, declare type
  3. Handle structs
-}

module StaticAnalysis.SMTInstrumentation (exprRel, statementRel, scDecs, parameterListDec, systemDecs, Z3Construct(..), SSAContext(..), Assert(..), Type(..), VarDeclaration(..)) where

  import CFG.CFG
  import Solidity.Solidity
  import Solidity.Parsing
  import Control.Monad
  import Text.Parsec
  import Text.Parsec.String
  import Data.Char hiding (DecimalNumber)
  import Data.List

  import Parseable

  import Data.List
  import Debug.Trace

  type VarName = String
-----------------

  instance Parseable VarName where
    display v = show v
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
  --we should also allow HexVal

  data StringVal = StringVal String
                  | StringVar String deriving (Eq, Ord, Show)
----------------
----------------

  instance Parseable StringVal where
  --  parser = --whitespace *> (SolidityCode <$> parser) <* whitespace <* eof
    display (StringVal s) = s
    display (StringVar v) = v
--------------------------------------------------------------------------------

  data StringRels  = SBase StringVal
                  | Concat StringRels StringRels deriving (Eq, Ord, Show)
---------------

  instance Parseable StringRels where
    display (SBase s) = display s
    display (Concat sr srr) = display sr ++ display srr
--------------------------------------------------------------------------------
  data ArrayVal = ArrayVar String deriving (Eq, Ord, Show)
    --            | SelectArray ArrayVal NumberRels
---------------

  instance Parseable ArrayVal where
    display (ArrayVar s) = s
  --  display (SelectArray arrayval numberRel) = "(select " ++ display arrayRel ++ " " ++ (display numberRel) ++ ")"
--------------------------------------------------------------------------------

  data ArrayRels = ArrayBase ArrayVal
            --    | Store ArrayVal GenericRelation GenericRelation
                | Select ArrayRels GenericRelation deriving (Eq, Ord, Show)
---------------

--  baseTypeOfArray :: ArrayRels -> Type
  --baseTypeOfArray (ArrayBase (ArrayVar _ typ)) = typ
--  baseTypeOfArray (Store arrayVal _ _) = baseTypeOfArray arrayVal
  --baseTypeOfArray (Select arrayVal _) = baseTypeOfArray arrayVal
---------------
  instance Parseable ArrayRels where
    display (ArrayBase arrayVal) = display arrayVal
--    display (Store arrayRel numberRel genRel) = "(store " ++ display arrayRel ++ " " ++ (display numberRel) ++ " " ++ display genRel ++ ")"
    display (Select arrayRel numberRel) = "(select " ++ display arrayRel ++ " " ++ (display numberRel) ++ ")"
--------------------------------------------------------------------------------

  data StructVal = StructVar String
                 | StructMemberSelect StructVal String deriving (Eq, Ord, Show)
---------------

  instance Parseable StructVal where
    display (StructVar s) = s
    display (StructMemberSelect struct child) = display struct ++ "." ++ child
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

  data MappingVal = MappingVar String Type Type deriving (Eq, Ord, Show)
            --      | SelectMap MappingVal GenericRelation
---------------

  instance Parseable MappingVal where
    display (MappingVar s _ _) = s
--    display (SelectMap s _ _) = "(select " ++ display rel ++ " " ++ (display genRel) ++ ")"
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
  data AssertRel = Assign GenericRelation GenericRelation | Rel ConditionalRels | ERROR deriving (Eq, Ord, Show)
---------------

  instance Parseable AssertRel where
    display (Assign s genRel) ="(= " ++ display s ++ " " ++ display genRel ++ ")"
    display (Rel genRel) = display genRel
    display (ERROR) = "ERROR"

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
    display (BitVector no) = "_ BitVector " ++ show no
    display (Fun t tt) = "(" ++ display t ++ ") " ++ "(" ++ display tt ++ ")"
    display (Array t tt) = "Array " ++ display t ++ " " ++ display tt
    display (UserSort name) = name
    display (Uninterpreted name) = name
--------------------------------------------------------------------------------

  data VarDeclaration = Dec String Type deriving (Eq, Ord, Show)
-------------

  instance Parseable VarDeclaration where
    display (Dec s (Fun t tt)) = "(declare-fun " ++ display (Fun t tt) ++ ")"
    display (Dec s (Uninterpreted ss)) = "(declare-const " ++ display s ++ " " ++ ss ++ ")"
    display (Dec s t) = "(declare-const " ++ s ++ " " ++ display t ++ ")"
--------------------------------------------------------------------------------

  data SortDeclaration = Struct String [(String, Type)] | Enum String [String] | UninterpretedSort String deriving (Eq, Ord, Show)
-------------

  instance Parseable SortDeclaration where
    display (Struct name vars) = "(declare-datatypes () ((" ++ name ++ " (mk-R" ++ (show $ length vars) ++ " " ++ createRecordType vars ++ "))))"
    display (Enum s types) = "(declare-datatypes () ((" ++ s ++ " " ++ (intercalate " " $ map display types) ++ ")))"--"(declare-datatypes () ((S A B C)))"
    display (UninterpretedSort sort) = "(declare-sort " ++ display sort ++ ")"
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
  scSortDecs :: SolidityCode -> [SortDeclaration]
  scSortDecs (SolidityCode (SourceUnit sourceUnits)) =  foldr (++) [] (map sourceUnit1SortDecs sourceUnits)
-------------
  sourceUnit1SortDecs :: SourceUnit1 -> [SortDeclaration]
  sourceUnit1SortDecs (SourceUnit1_ContractDefinition contractDefinition) = contractDefinitionSortDecs contractDefinition
-------------
  contractDefinitionSortDecs :: ContractDefinition -> [SortDeclaration]
  contractDefinitionSortDecs (ContractDefinition _ _ _ contractParts) = foldr (++) [] (map contractPartsSortDec contractParts)
-------------
  contractPartsSortDec :: ContractPart -> [SortDeclaration]
  contractPartsSortDec (ContractPartEnumDefinition (Identifier id) enumValues) = [(Enum id (map unIdentifier enumValues))]
  contractPartsSortDec (ContractPartStructDefinition (Identifier id) varDecs) = [(Struct id [(idd, typeOfTypeName typeName) | (VariableDeclaration typeName _ (Identifier idd)) <- varDecs])]
  contractPartsSortDec _ = []
-------------
-------------

  --TODO some values are global, others intraprocedural
  systemDecs :: SSAContext
  systemDecs = [(Dec "msg.sender" Intt, 0), (Dec "msg.value" Intt, 0), (Dec "balance" Intt, 0), (Dec "this.balance" Intt, 0)]
-------------
  scDecs :: SolidityCode -> (SSAContext, [AssertRel])
  scDecs (SolidityCode (SourceUnit sourceUnits)) = sourceUnit1Decs [] sourceUnits
-------------
  sourceUnit1Decs :: SSAContext -> [SourceUnit1] -> (SSAContext, [AssertRel])
  sourceUnit1Decs ssaContext ((SourceUnit1_ContractDefinition contractDefinition):rest) = let (nextSSAContext, nextAsserts) = contractDefinitionDecs ssaContext contractDefinition
                                                                                              (restSSAContext, restAsserts) = sourceUnit1Decs nextSSAContext rest
                                                                                            in (restSSAContext, nextAsserts ++ restAsserts)
  sourceUnit1Decs ssaContext (_:rest) = sourceUnit1Decs ssaContext rest
  sourceUnit1Decs ssaContext [] = (ssaContext, [])
-------------
  contractDefinitionDecs :: SSAContext -> ContractDefinition -> (SSAContext, [AssertRel])
  contractDefinitionDecs ssaContext (ContractDefinition _ _ _ contractParts) = let sortDecs = foldr (++) [] (map contractPartsSortDec contractParts)
                                                                      in contractPartsDec sortDecs ssaContext contractParts
-------------
  contractPartsDec :: [SortDeclaration] -> SSAContext -> [ContractPart] -> (SSAContext, [AssertRel])
  contractPartsDec sortDecs ssaContext ((ContractPartStateVariableDeclaration stateVariableDeclaration):parts) = let (newSSAContext, assertRel) = (stateVariableDec sortDecs ssaContext stateVariableDeclaration)
                                                                                                                     (otherPartsSSA, otherPartsAsserts) = contractPartsDec sortDecs newSSAContext parts
                                                                                                                    in (otherPartsSSA, otherPartsAsserts ++ assertRel)


  contractPartsDec sortDecs ssaContext (_:parts) = contractPartsDec sortDecs ssaContext parts
  contractPartsDec _ ssaContext _ = (ssaContext, [])
-------------
--TODO go through variable decs after and add type conditions, e.g. uint256 variables must be less that 2^256, and bigger or equal to 0
  stateVariableDec :: [SortDeclaration] -> SSAContext -> StateVariableDeclaration -> (SSAContext, [AssertRel])
  stateVariableDec sortDecs ssaContext (StateVariableDeclaration typeName _ (Identifier varName) Nothing) = ([(Dec varName (typeOfTypeName typeName),0)] ++ ssaContext, [])
  stateVariableDec sortDecs ssaContext (StateVariableDeclaration typeName _ (Identifier varName) (Just expr)) = let newSSAContext = ssaContext ++ [(Dec varName (typeOfTypeName typeName), 0)]
                                                                                                                    (decs, maybeAssertRel, newerSSAContext) = exprRel sortDecs newSSAContext (Binary "=" (Literal (PrimaryExpressionIdentifier (Identifier varName))) expr)
                                                                                                                    newAsserts = case maybeAssertRel of
                                                                                                                                               Nothing -> []
                                                                                                                                               Just assertRel -> [assertRel]
                                                                                                                  in (newerSSAContext, newAsserts)
  stateVariableDec sortDecs ssaContext _ = (ssaContext, [])

-------------
  parameterListDec :: [SortDeclaration] -> SSAContext -> ParameterList -> SSAContext
  parameterListDec sortDecs ssaContext (ParameterList []) = ssaContext
  parameterListDec sortDecs ssaContext (ParameterList ((Parameter typ (Just (Identifier name))):rest)) = let newSSAContext = [(Dec name (typeOfTypeName typ), 0)] ++ ssaContext
                                                                                                    in parameterListDec sortDecs newSSAContext (ParameterList rest)
-------------
  parameterListDec sortDecs ssaContext (ParameterList (_:rest)) = parameterListDec sortDecs ssaContext (ParameterList rest)
-------------
  type SSAContext = [(VarDeclaration, Int)]
-------------
  updateSSAVarCounter :: String -> SSAContext -> SSAContext
  updateSSAVarCounter var ssaContext = let updatedVariable = [(Dec v t, n + 1) | (Dec v t,n) <- ssaContext, v == var]
                                           contextWithVariableCounter = [(Dec v t,n) | (Dec v t,n) <- ssaContext, v /= var]
                                          in if null updatedVariable
                                              then [(Dec var (Uninterpreted "UNDECLARED"), 0)] ++ contextWithVariableCounter
                                              else updatedVariable ++ contextWithVariableCounter

  getCurrentFormOfVar :: String -> SSAContext -> String
  getCurrentFormOfVar var ssaContext = let nos = [n | (Dec v _, n) <- ssaContext, v == var]
                                        in if null nos
                                            then var ++ "0"
                                            else var ++ (show $ head nos)

  getNextFormOfVar :: String -> SSAContext -> (String, SSAContext)
  getNextFormOfVar var ssaContext = let nos = [(Dec v t, n) | (Dec v t, n) <- ssaContext, v == var]
                                      in if null nos
                                          then (var ++ "0", [(Dec var (Uninterpreted "UNDECLARED"), 0)] ++ ssaContext)
                                          else (var ++ (show $ head [n | (Dec v t, n) <- nos]), (ssaContext \\ nos) ++ [(Dec v t, n + 1) | (Dec v t, n) <- nos])

  --renameVar :: String -> String ->
-------------

--  data BasicValue = Val String | Var String

  primaryExprRelCurrentVar :: SSAContext -> PrimaryExpression -> Maybe GenericRelation
  primaryExprRelCurrentVar ssaContext (PrimaryExpressionBooleanLiteral (BooleanLiteral literal)) = (Just $ Cond $ CBase $ BoolVal literal)
  primaryExprRelCurrentVar ssaContext (PrimaryExpressionNumberLiteral ((NumberLiteralDec stringNum Nothing))) = (Just $ Numb $ NBase $ IntVal stringNum)
  primaryExprRelCurrentVar ssaContext (PrimaryExpressionNumberLiteral numberMaybeWithUnits) = (Just $ Other (display numberMaybeWithUnits)) --TODO
  primaryExprRelCurrentVar ssaContext (PrimaryExpressionHexLiteral (HexLiteral literal)) = (Just $ Other literal) --TODO
  primaryExprRelCurrentVar ssaContext (PrimaryExpressionIdentifier (Identifier literal)) = (Just $ Other (getCurrentFormOfVar literal ssaContext))
  primaryExprRelCurrentVar ssaContext (PrimaryExpressionTupleExpression tupleExpression) = (Just $ Other $ display tupleExpression)
  primaryExprRelCurrentVar ssaContext (PrimaryExpressionStringLiteral (StringLiteral literal)) = (Just $ Strings $ SBase $ StringVal literal)
  primaryExprRelCurrentVar ssaContext (PrimaryExpressionElementaryTypeNameExpression typeName) = (Nothing)

  primaryExprRelNextVar :: SSAContext -> PrimaryExpression -> (Maybe GenericRelation, SSAContext)
  primaryExprRelNextVar ssaContext (PrimaryExpressionBooleanLiteral (BooleanLiteral literal)) = (Just $ Cond $ CBase $ BoolVal literal, ssaContext)
  primaryExprRelNextVar ssaContext (PrimaryExpressionNumberLiteral ((NumberLiteralDec stringNum Nothing))) = (Just $ Numb $ NBase $ IntVal stringNum, ssaContext)
  primaryExprRelNextVar ssaContext (PrimaryExpressionNumberLiteral numberMaybeWithUnits) = (Just $ Other (display numberMaybeWithUnits), ssaContext) --TODO
  primaryExprRelNextVar ssaContext (PrimaryExpressionHexLiteral (HexLiteral literal)) = (Just $ Other literal, ssaContext) --TODO
  primaryExprRelNextVar ssaContext (PrimaryExpressionIdentifier (Identifier literal)) = let (nextVar, nextSSAContext) = getNextFormOfVar literal ssaContext
                                                                                    in (Just $ Other nextVar, nextSSAContext)
  primaryExprRelNextVar ssaContext (PrimaryExpressionTupleExpression tupleExpression) = (Just $ Other $ display tupleExpression, ssaContext)
  primaryExprRelNextVar ssaContext (PrimaryExpressionStringLiteral (StringLiteral literal)) = (Just $ Strings $ SBase $ StringVal literal, ssaContext)
  primaryExprRelNextVar ssaContext (PrimaryExpressionElementaryTypeNameExpression typeName) = (Nothing, ssaContext)
--------------
--   data GenericRelation = Cond ConditionalRels | Numb NumberRels | Arrays ArrayRels | Mapping MappingRels | Strings StringRels | Other String  deriving (Eq, Ord, Show)
  --data AssertRel = Assign String GenericRelation | Rel ConditionalRels | ERROR deriving (Eq, Ord, Show)

--here deal with anything that can be represented as a generic relation
--focus on computations, but not changes in memory/storate
--TODO add new variable declaration
  exprRelGenRelationNextVar :: [SortDeclaration] -> SSAContext -> Expression -> (Maybe GenericRelation, SSAContext)
  exprRelGenRelationNextVar sortDecs ssaContext (Literal primaryExpr) = primaryExprRelNextVar ssaContext primaryExpr
  exprRelGenRelationNextVar sortDecs ssaContext (MemberAccess expr (Identifier member)) = let (maybeStructVal, newSSAContext) = exprRelGenRelationNextVar sortDecs ssaContext expr
                                                                                              newMaybeGenRel = case maybeStructVal of
                                                                                                                --  Just (Other var) -> Just $ Structs $ (MemberSelect (StructBase $ StructVar var) member)
                                                                                                                  Just (Structs (MemberSelect (StructBase (StructVar var)) memberr)) -> Just $ Structs $ MemberSelect (MemberSelect (StructBase $ StructVar var) memberr) member
                                                                                                                  Just v -> Just $ Structs $ (MemberSelect (StructBase $ StructVar (display v)) member)
                                                                                                                  _ -> trace ("UYTRESDV") (Just $ Other "ERROR")
                                                                                            in (newMaybeGenRel, newSSAContext)

  exprRelGenRelationNextVar sortDecs ssaContext (Binary "[]" expr indexExpr) = let (maybeStructVal, newSSAContext) = exprRelGenRelationNextVar sortDecs ssaContext expr
                                                                                   maybeIndexGenrel = exprRelGenRelation sortDecs ssaContext indexExpr
                                                                                   wholeGenRel = case maybeIndexGenrel of
                                                                                                        Just genRel ->  case maybeStructVal of
                                                                                                                            --    Just (Other var) -> Just $ Arrays $ Select (ArrayBase $ ArrayVar var) genRel
                                                                                                                                Just (Arrays (Select arrayRel numberRel)) -> Just $ Arrays $ Select (Select arrayRel numberRel) genRel
                                                                                                                                Just v -> Just $ Arrays $ Select (ArrayBase $ ArrayVar (display v)) genRel
                                                                                                                                v -> trace "GHFDSF" (Just $ Other "ERROR")
                                                                                                        Nothing -> Nothing
                                                                            in (wholeGenRel, newSSAContext)

  exprRelGenRelationNextVar _ ssaContext _ = (Nothing, ssaContext)


  --TODO bitwise operations and exponentiation
  exprRelGenRelation :: [SortDeclaration] -> SSAContext -> Expression -> Maybe GenericRelation
  exprRelGenRelation sortDecs ssaContext (Literal primaryExpr) = primaryExprRelCurrentVar ssaContext primaryExpr

  exprRelGenRelation sortDecs ssaContext (Unary "!" expr) = case exprRelGenRelation sortDecs ssaContext expr of
                                                                        Just (Cond condRel) -> Just (Cond $ Not condRel)
                                                                        Just v -> trace ("! second cond " ++ show v) (Just (Cond $ Not (CBase $ BoolVar (display v))))
                                                                        v -> trace ("!= error: " ++ show v) (Just $ Other "ERROR")


  exprRelGenRelation sortDecs ssaContext (Binary "[]" expr exprr) = case (exprRelGenRelation sortDecs ssaContext expr, exprRelGenRelation sortDecs ssaContext exprr) of
                                                                          (Just v, Just vv) -> trace ("Just v arrays: " ++ show v) Just $ Arrays $ Select (ArrayBase $ ArrayVar (display v)) vv
                                                                          _ -> trace "3er544rt5rgfv" (Just $ Other "ERROR")

  exprRelGenRelation sortDecs ssaContext (Binary "+" expr exprr) = case (exprRelGenRelation sortDecs ssaContext expr, exprRelGenRelation sortDecs ssaContext exprr) of
                                                                          (Just (Numb rel), Just (Numb rell)) -> Just (Numb $ Plus rel rell)
                                                                          (Just (Strings rel), Just (Strings rell)) -> Just (Strings $ Concat rel rell)
                                                                          (Just v, Just vv) -> Just (Numb $ Plus (NBase $ IntVar (display v)) (NBase $ IntVar (display vv))) --not necessarily a number here TODO check type of vaiable from ssaContext
                                                                          _ -> Just $ Other "ERROR"

  exprRelGenRelation sortDecs ssaContext (Binary "-" expr exprr) = case (exprRelGenRelation sortDecs ssaContext expr, exprRelGenRelation sortDecs ssaContext exprr) of
                                                                          (Just (Numb rel), Just (Numb rell)) -> Just (Numb $ Minus rel rell)
                                                                          (Just v, Just vv) -> Just (Numb $ Minus (NBase $ IntVar (display v)) (NBase $ IntVar (display vv)))
                                                                          _ -> Just $ Other "ERROR"


  exprRelGenRelation sortDecs ssaContext (Binary "*" expr exprr) = case (exprRelGenRelation sortDecs ssaContext expr, exprRelGenRelation sortDecs ssaContext exprr) of
                                                                          (Just (Numb rel), Just (Numb rell)) -> Just (Numb $ Multiply rel rell)
                                                                          (Just v, Just vv) -> Just (Numb $ Multiply (NBase $ IntVar (display v)) (NBase $ IntVar (display vv)))
                                                                          _ -> Just $ Other "ERROR"


  exprRelGenRelation sortDecs ssaContext (Binary "/" expr exprr) = case (exprRelGenRelation sortDecs ssaContext expr, exprRelGenRelation sortDecs ssaContext exprr) of
                                                                          (Just (Numb rel), Just (Numb rell)) -> Just (Numb $ Div rel rell)
                                                                          (Just v, Just vv) -> Just (Numb $ Div (NBase $ IntVar (display v)) (NBase $ IntVar (display vv)))
                                                                          _ -> Just $ Other "ERROR"


  exprRelGenRelation sortDecs ssaContext (Binary "%" expr exprr) = case (exprRelGenRelation sortDecs ssaContext expr, exprRelGenRelation sortDecs ssaContext exprr) of
                                                                          (Just (Numb rel), Just (Numb rell)) -> Just (Numb $ Mod rel rell)
                                                                          (Just v, Just vv) -> Just (Numb $ Mod (NBase $ IntVar (display v)) (NBase $ IntVar (display vv)))
                                                                          _ -> Just $ Other "ERROR"

  --exprRelGenRelation sortDecs ssaContext (Binary "^" expr exprr) = case (exprRelGenRelation sortDecs ssaContext expr, exprRelGenRelation sortDecs ssaContext exprr) of
    --                                                                      (Just (Numb rel), Just (Numb rell)) -> Just (Numb $ PowerOf rel rell)
      --                                                                    (Just v, Just vv) -> Just (Numb $ PowerOf (NBase $ IntVar (display v)) (NBase $ IntVar (display vv)))
        --                                                                  _ -> Just $ Other "ERROR"

  exprRelGenRelation sortDecs ssaContext (Binary "&" expr exprr) = case (exprRelGenRelation sortDecs ssaContext expr, exprRelGenRelation sortDecs ssaContext exprr) of
                                                                          (Just (Cond rel), Just (Cond rell)) -> Just (Cond $ And rel rell)
                                                                          (Just v, Just vv) -> Just (Cond $ And (CBase $ BoolVar (display v)) (CBase $ BoolVar (display vv)))
                                                                          _ -> Just $ Other "ERROR"

  exprRelGenRelation sortDecs ssaContext (Binary "&&" expr exprr) = exprRelGenRelation sortDecs ssaContext (Binary "&" expr exprr)

  exprRelGenRelation sortDecs ssaContext (Binary "|" expr exprr) = case (exprRelGenRelation sortDecs ssaContext expr, exprRelGenRelation sortDecs ssaContext exprr) of
                                                                          (Just (Cond rel), Just (Cond rell)) -> Just (Cond $ Or rel rell)
                                                                          (Just v, Just vv) -> Just (Cond $ Or (CBase $ BoolVar (display v)) (CBase $ BoolVar (display vv)))
                                                                          v -> (Just $ Other "ERROR")

  exprRelGenRelation sortDecs ssaContext (Binary "||" expr exprr) = exprRelGenRelation sortDecs ssaContext (Binary "|" expr exprr)

  exprRelGenRelation sortDecs ssaContext (Binary ">" expr exprr) = case (exprRelGenRelation sortDecs ssaContext expr, exprRelGenRelation sortDecs ssaContext exprr) of
                                                                          (Just (Numb rel), Just (Numb rell)) -> Just (Cond $ Greater rel rell)
                                                                          (Just v, Just vv) -> Just (Cond $ Greater (NBase $ IntVar (display v)) (NBase $ IntVar (display vv)))
                                                                          _ -> Just $ Other "ERROR"


  exprRelGenRelation sortDecs ssaContext (Binary ">=" expr exprr) = case (exprRelGenRelation sortDecs ssaContext expr, exprRelGenRelation sortDecs ssaContext exprr) of
                                                                          (Just (Numb rel), Just (Numb rell)) -> Just (Cond $ GreaterOrEqual rel rell)
                                                                          (Just v, Just vv) -> Just (Cond $ GreaterOrEqual (NBase $ IntVar (display v)) (NBase $ IntVar (display vv)))
                                                                          _ -> Just $ Other "ERROR"


  exprRelGenRelation sortDecs ssaContext (Binary "<" expr exprr) = case (exprRelGenRelation sortDecs ssaContext expr, exprRelGenRelation sortDecs ssaContext exprr) of
                                                                          (Just (Numb rel), Just (Numb rell)) -> Just (Cond $ Less rel rell)
                                                                          (Just v, Just vv) -> Just (Cond $ Less (NBase $ IntVar (display v)) (NBase $ IntVar (display vv)))
                                                                          _ -> Just $ Other "ERROR"


  exprRelGenRelation sortDecs ssaContext (Binary "<=" expr exprr) = case (exprRelGenRelation sortDecs ssaContext expr, exprRelGenRelation sortDecs ssaContext exprr) of
                                                                          (Just (Numb rel), Just (Numb rell)) -> Just (Cond $ LessOrEqual rel rell)
                                                                          (Just v, Just vv) -> Just (Cond $ LessOrEqual (NBase $ IntVar (display v))  (NBase $ IntVar (display vv)))
                                                                          _ -> Just $ Other "ERROR"


  exprRelGenRelation sortDecs ssaContext (Binary "==" expr exprr) = (case (exprRelGenRelation sortDecs ssaContext expr, exprRelGenRelation sortDecs ssaContext exprr) of
                                                                                                    (Just rel, Just rell) -> Just (Cond $ Equals rel rell)
                                                                                                    (Just v, Just vv) -> Just (Cond $ Equals (Cond $ CBase $ BoolVar (display v)) (Cond $ CBase $ BoolVar (display vv)))
                                                                                                    _ -> Just $ Other "ERROR")

  exprRelGenRelation sortDecs ssaContext (Binary "!=" expr exprr) = case (exprRelGenRelation sortDecs ssaContext expr, exprRelGenRelation sortDecs ssaContext exprr) of
                                                                          (Just rel, Just rell) -> Just (Cond $ Not $ Equals rel rell)
                                                                          (Just v, Just vv) -> Just (Cond $ Not (Equals (Cond $ CBase $ BoolVar (display v)) (Cond $ CBase $ BoolVar (display vv))))
                                                                          v -> (Just $ Other "ERROR")

  exprRelGenRelation sortDecs ssaContext (MemberAccess expr (Identifier member)) = let maybeStructVal = exprRelGenRelation sortDecs ssaContext expr
                                                                                       newMaybeGenRel = case maybeStructVal of
                                                                                                                --  Just (Other var) -> Just $ Structs $ (MemberSelect (StructBase $ StructVar var) member)
                                                                                                                  Just (Structs (MemberSelect (StructBase (StructVar var)) memberr)) -> Just $ Structs $ MemberSelect (MemberSelect (StructBase $ StructVar var) memberr) member
                                                                                                                  Just v -> Just $ Structs $ (MemberSelect (StructBase $ StructVar (display v)) member)
                                                                                                                  _ -> trace ("UYTRESDV") (Just $ Other "ERROR")
                                                                                    in newMaybeGenRel

  exprRelGenRelation _ _ _ = Nothing


--here deal with anything that can be represented as an assertrelation
--focus on changes to storage like assignment, delete (create a new version of the variable empty at the deleted index, or an empty map, see exact behaviour), storing
--TODO only generate new / next var if the var is used on the right-hand side
--TODO deal with delete
--TODO pre-parse the ternary operator into if-else clauses
--TODO difference betwee ++x; and x++; this depends on context, e.g. y = x++; and y' = ++x; will have different values. x++ rreturns the value of x then adds 1 to it, while ++x adds 1 to x and returns x
  exprRel :: [SortDeclaration] -> SSAContext -> Expression -> ([VarDeclaration], Maybe AssertRel, SSAContext)

  exprRel sortDecs ssaContext (Unary "++" expr) = exprRel sortDecs ssaContext (Binary "=" expr (Binary "+" expr (Literal (PrimaryExpressionNumberLiteral (NumberLiteralDec "1" Nothing)))))
  exprRel sortDecs ssaContext (Unary "--" expr) = exprRel sortDecs ssaContext (Binary "=" expr (Binary "-" expr (Literal (PrimaryExpressionNumberLiteral (NumberLiteralDec "1" Nothing)))))

  exprRel sortDecs ssaContext (Binary "+=" lhs rhs) = exprRel sortDecs ssaContext (Binary "=" lhs (Binary "+" lhs rhs))
  exprRel sortDecs ssaContext (Binary "-=" lhs rhs) = exprRel sortDecs ssaContext (Binary "=" lhs (Binary "-" lhs rhs))
  exprRel sortDecs ssaContext (Binary "*=" lhs rhs) = exprRel sortDecs ssaContext (Binary "=" lhs (Binary "*" lhs rhs))
  exprRel sortDecs ssaContext (Binary "/=" lhs rhs) = exprRel sortDecs ssaContext (Binary "=" lhs (Binary "/" lhs rhs))
  exprRel sortDecs ssaContext (Binary "&=" lhs rhs) = exprRel sortDecs ssaContext (Binary "=" lhs (Binary "&" lhs rhs))
  exprRel sortDecs ssaContext (Binary "|=" lhs rhs) = exprRel sortDecs ssaContext (Binary "=" lhs (Binary "|" lhs rhs))
  exprRel sortDecs ssaContext (Binary "%=" lhs rhs) = exprRel sortDecs ssaContext (Binary "=" lhs (Binary "%" lhs rhs))

  exprRel sortDecs ssaContext (Binary "=" lhs rhs) = let (maybeLHSGenRel, newSSAContext) = (exprRelGenRelationNextVar sortDecs ssaContext lhs)
                                                         maybeRHSGenRel = (exprRelGenRelation sortDecs ssaContext rhs)
                                                       in case (maybeLHSGenRel, maybeRHSGenRel) of
                                                                        (Nothing, _) -> ([], Just $ ERROR, [])
                                                                        (_, Nothing) -> ([], Just $ ERROR, [])
                                                                        (Just genRel, Just genRell) -> ([], Just $ Assign genRel genRell, newSSAContext)

  exprRel sortDecs ssaContext expr = let maybeGenRel = exprRelGenRelation sortDecs ssaContext expr
                                        in case maybeGenRel of
                                                  Nothing -> ([], Nothing, ssaContext)
                                                  Just (Cond rel) -> ([], Just $ Rel rel, ssaContext)
                                                  v -> trace ("exprRel: " ++ show v) ([], Just ERROR, ssaContext)
--TODO  exprRel sortDecs ssaContext (Unary "delete" expr) =
  exprRel sortDecs ssaContext _ = ([], Nothing, ssaContext)

--I think we don t need the var dec
  statementRel :: [SortDeclaration] -> SSAContext -> Statement -> ([VarDeclaration], Maybe AssertRel, SSAContext)
  statementRel sortDec ssaContext (InlineAssemblyStatement _ _) = ([], Just $ ERROR, [])
  statementRel sortDec ssaContext (Throw) = ([], Just $ ERROR, [])
  --TODO is there something to do here with return variable defined at level of function definition?
  statementRel sortDec ssaContext (Return _) = ([], Nothing, ssaContext)
  statementRel sortDec ssaContext (SimpleStatementExpression expression) = exprRel sortDec ssaContext expression
  statementRel sortDec ssaContext (SimpleStatementVariableDeclaration (variableDec) Nothing) = let varName = unIdentifier $ variableDeclarationName variableDec
                                                                                                   varType = typeOfTypeName $ variableDeclarationType variableDec
                                                                                                  in ([Dec varName varType], Nothing, [((Dec varName varType), 0)] ++ ssaContext)
  statementRel sortDec ssaContext (SimpleStatementVariableDeclaration (variableDec) (Just expr)) = let varName = variableDeclarationName variableDec
                                                                                                       varType = typeOfTypeName $ variableDeclarationType variableDec
                                                                                                       ssaContextWithNewVarDec = [(Dec (unIdentifier varName) varType,0)] ++ ssaContext
                                                                                                       (assignDecs, maybeAssignAssertRel, assignSSAContext) = exprRel sortDec ssaContextWithNewVarDec (Binary "=" (Literal (PrimaryExpressionIdentifier varName)) expr)
                                                                                                       (decAssignDecs, _, decAssignSSAContext) = statementRel sortDec assignSSAContext (SimpleStatementVariableDeclaration (variableDec) Nothing)
                                                                                                    in (assignDecs ++ decAssignDecs, maybeAssignAssertRel,  decAssignSSAContext)
  statementRel _ ssaContext _ = ([], Nothing, ssaContext)
  --TODO  ?? statementRel sortDec ssaContext (SimpleStatementVariableList IdentifierList (Maybe Expression)) = exprRel sortDec ssaContext expression
