{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}

{-TODO

  1. Push in arrays modeled as store
  2. Array length function, declare type
  3. Handle structs
-}

module SMT.SolidityToSMTLib2 where

  import DEA.DEA
  import CFG.CFG
  import Solidity.Solidity
  import SMT.SMTLib2
  import Debug.Trace
-------------
--TODO default smart contract system variables, i.e. this.address or is it (address) this
--TODO need to deal with inheritance (vardecs and sortdecs of parent contract need to be replicated in child)
-------------
-------------
--Default system function-specific variables
-------------
  functionSystemDecs :: [VarDeclaration]
  functionSystemDecs = [Dec "msg.sender" (BitVector (20*8)), Dec "msg.value" Intt, Dec "balance" Intt, Dec "this.balance" Intt, Dec "now" Intt]
-------------
  functionDecs :: FunctionSignature -> [VarDeclaration]
  functionDecs (FunctionSignature _ _ parameterList returnParamList) = (parameterListDec parameterList) ++ (parameterListDec returnParamList)
-------------
--Getting required sort declarations from a smart contract (used to model structs)
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
--Custom user smart contract variables with default value
-------------
  globalSCDecs :: SolidityCode -> ([VarDeclaration], [AssertRel])
  globalSCDecs (SolidityCode (SourceUnit sourceUnits)) = sourceUnit1Decs sourceUnits
  globalSCDecs _ = ([],[])
-------------
  sourceUnit1Decs :: [SourceUnit1] -> ([VarDeclaration], [AssertRel])
  sourceUnit1Decs [] = ([], [])
  sourceUnit1Decs ((SourceUnit1_ContractDefinition contractDefinition):rest) = let (nextVarDecs, nextAsserts) = contractDefinitionDecs contractDefinition
                                                                                   (restVarDecs, restAsserts) = sourceUnit1Decs rest
                                                                                 in (nextVarDecs ++ restVarDecs, nextAsserts ++ restAsserts)
  sourceUnit1Decs (_:rest) = sourceUnit1Decs rest
-------------
  contractDefinitionDecs :: ContractDefinition -> ([VarDeclaration], [AssertRel])
  contractDefinitionDecs (ContractDefinition _ _ _ contractParts) = contractPartsDec contractParts
-------------
  contractPartsDec :: [ContractPart] -> ([VarDeclaration], [AssertRel])
  contractPartsDec ((ContractPartStateVariableDeclaration stateVariableDeclaration):parts) = let (varDecs, assertRels) = (stateVariableDec stateVariableDeclaration)
                                                                                                 (othervarDecs, otherAssertRels) = contractPartsDec parts
                                                                                              in (varDecs ++ othervarDecs, assertRels ++ otherAssertRels)


  contractPartsDec (_:parts) = contractPartsDec parts
  contractPartsDec _ = ([],[])
-------------
-------------
  statementRel :: Statement -> ([VarDeclaration], [AssertRel])
  statementRel (InlineAssemblyStatement _ _) = ([], [ERROR])
  statementRel (Throw) = ([], [ERROR])
  --TODO is there something to do here with return variable defined at level of function definition?
  statementRel (Return _) = ([], [])
  statementRel (SimpleStatementExpression expression) = case exprRel expression of
                                                          Nothing -> ([],[])
                                                          Just assertRel -> ([],[assertRel])

  statementRel (SimpleStatementVariableDeclaration (variableDec) Nothing) = let varName = unIdentifier $ variableDeclarationName variableDec
                                                                                varType = typeOfTypeName $ variableDeclarationType variableDec
                                                                              in ([Dec varName varType], [])

  statementRel (SimpleStatementVariableDeclaration (variableDec) (Just expr)) = let varName = variableDeclarationName variableDec
                                                                                    varType = typeOfTypeName $ variableDeclarationType variableDec
                                                                                    (_,assertRels) = statementRel (SimpleStatementExpression $ Binary "=" (Literal (PrimaryExpressionIdentifier varName)) expr)
                                                                                    (decAssignDecs, assertRelss) = statementRel (SimpleStatementVariableDeclaration (variableDec) Nothing)
                                                                                  in (decAssignDecs, assertRels ++ assertRelss)
  statementRel _ = ([], [])
  --TODO  ?? statementRel sortDec ssaContext (SimpleStatementVariableList IdentifierList (Maybe Expression)) = exprRel sortDec ssaContext expression
-------------
-------------
--TODO go through variable decs after and add type conditions, e.g. uint256 variables must be less that 2^256, and bigger or equal to 0
  stateVariableDec ::  StateVariableDeclaration -> ([VarDeclaration], [AssertRel])
  stateVariableDec (StateVariableDeclaration typeName _ (Identifier varName) Nothing) = ([Dec varName (typeOfTypeName typeName)], [])
  stateVariableDec (StateVariableDeclaration typeName _ (Identifier varName) (Just expr)) = let varDec = [Dec varName (typeOfTypeName typeName)]
                                                                                                maybeAssertRel = exprRel (Binary "=" (Literal (PrimaryExpressionIdentifier (Identifier varName))) expr)
                                                                                                newAsserts = case maybeAssertRel of
                                                                                                                Nothing -> []
                                                                                                                Just assertRel -> [assertRel]
                                                                                               in (varDec, newAsserts)
  stateVariableDec _ = ([], [])

-------------
  parameterListDec :: ParameterList -> [VarDeclaration]
  parameterListDec (ParameterList []) = []
  parameterListDec (ParameterList ((Parameter typ (Just (Identifier name))):rest)) = ([Dec name (typeOfTypeName typ)] ++ (parameterListDec (ParameterList rest)))
-------------
  parameterListDec (ParameterList (x:rest)) = (parameterListDec (ParameterList rest))
-------------
-------------
--  data BasicValue = Val String | Var String

  primaryExprRel :: PrimaryExpression -> Maybe GenericRelation
  primaryExprRel (PrimaryExpressionBooleanLiteral (BooleanLiteral literal)) = (Just $ Cond $ CBase $ BoolVal literal)
  primaryExprRel (PrimaryExpressionNumberLiteral ((NumberLiteralDec stringNum Nothing))) = (Just $ Numb $ NBase $ IntVal stringNum)
  primaryExprRel (PrimaryExpressionNumberLiteral numberMaybeWithUnits) = (Just $ Other (display numberMaybeWithUnits)) --TODO
  primaryExprRel (PrimaryExpressionHexLiteral (HexLiteral literal)) = (Just $ Other literal) --TODO
  primaryExprRel (PrimaryExpressionIdentifier (Identifier literal)) = (Just $ Other literal)
  primaryExprRel (PrimaryExpressionTupleExpression tupleExpression) = (Just $ Other $ display tupleExpression)
  primaryExprRel (PrimaryExpressionStringLiteral (StringLiteral literal)) = (Just $ Strings $ SBase $ StringVal literal)
  primaryExprRel (PrimaryExpressionElementaryTypeNameExpression typeName) = (Nothing)

--------------
--   data GenericRelation = Cond ConditionalRels | Numb NumberRels | Arrays ArrayRels | Mapping MappingRels | Strings StringRels | Other String  deriving (Eq, Ord, Show)
  --data AssertRel = Assign String GenericRelation | Rel ConditionalRels | ERROR deriving (Eq, Ord, Show)


  --TODO bitwise operations and exponentiation
  exprRelGenRelation :: Expression -> Maybe GenericRelation
  exprRelGenRelation (Literal primaryExpr) = primaryExprRel primaryExpr
  exprRelGenRelation (MemberAccess (Literal (PrimaryExpressionIdentifier (Identifier "msg"))) (Identifier idd)) = Just $ Other ("msg." ++ idd)

  exprRelGenRelation (Unary "!" expr) = case exprRelGenRelation expr of
                                                                        Just (Cond condRel) -> Just (Cond $ Not condRel)
                                                                        Just v -> (Just (Cond $ Not (CBase $ BoolVar (display v))))
                                                                        v -> (Just $ Other "ERROR")


  exprRelGenRelation (Binary "[]" expr exprr) = case (exprRelGenRelation expr, exprRelGenRelation exprr) of
                                                                          (Just v, Just vv) -> Just $ Arrays $ Select (ArrayBase $ ArrayVar (display v)) vv
                                                                          _ -> (Just $ Other "ERROR")

  exprRelGenRelation (Binary "+" expr exprr) = case (exprRelGenRelation expr, exprRelGenRelation exprr) of
                                                                          (Just (Numb rel), Just (Numb rell)) -> Just (Numb $ Plus rel rell)
                                                                          (Just (Strings rel), Just (Strings rell)) -> Just (Strings $ Concat rel rell)
                                                                          (Just v, Just vv) -> Just (Numb $ Plus (NBase $ IntVar (display v)) (NBase $ IntVar (display vv))) --not necessarily a number here TODO check type of vaiable from ssaContext
                                                                          _ -> Just $ Other "ERROR"

  exprRelGenRelation (Binary "-" expr exprr) = case (exprRelGenRelation expr, exprRelGenRelation exprr) of
                                                                          (Just (Numb rel), Just (Numb rell)) -> Just (Numb $ Minus rel rell)
                                                                          (Just v, Just vv) -> Just (Numb $ Minus (NBase $ IntVar (display v)) (NBase $ IntVar (display vv)))
                                                                          _ -> Just $ Other "ERROR"


  exprRelGenRelation (Binary "*" expr exprr) = case (exprRelGenRelation expr, exprRelGenRelation exprr) of
                                                                          (Just (Numb rel), Just (Numb rell)) -> Just (Numb $ Multiply rel rell)
                                                                          (Just v, Just vv) -> Just (Numb $ Multiply (NBase $ IntVar (display v)) (NBase $ IntVar (display vv)))
                                                                          _ -> Just $ Other "ERROR"


  exprRelGenRelation (Binary "/" expr exprr) = case (exprRelGenRelation expr, exprRelGenRelation exprr) of
                                                                          (Just (Numb rel), Just (Numb rell)) -> Just (Numb $ Div rel rell)
                                                                          (Just v, Just vv) -> Just (Numb $ Div (NBase $ IntVar (display v)) (NBase $ IntVar (display vv)))
                                                                          _ -> Just $ Other "ERROR"


  exprRelGenRelation (Binary "%" expr exprr) = case (exprRelGenRelation expr, exprRelGenRelation exprr) of
                                                                          (Just (Numb rel), Just (Numb rell)) -> Just (Numb $ Mod rel rell)
                                                                          (Just v, Just vv) -> Just (Numb $ Mod (NBase $ IntVar (display v)) (NBase $ IntVar (display vv)))
                                                                          _ -> Just $ Other "ERROR"

  --exprRelGenRelation ssaContext (Binary "^" expr exprr) = case (exprRelGenRelation ssaContext expr, exprRelGenRelation ssaContext exprr) of
    --                                                                      (Just (Numb rel), Just (Numb rell)) -> Just (Numb $ PowerOf rel rell)
      --                                                                    (Just v, Just vv) -> Just (Numb $ PowerOf (NBase $ IntVar (display v)) (NBase $ IntVar (display vv)))
        --                                                                  _ -> Just $ Other "ERROR"

  exprRelGenRelation (Binary "&" expr exprr) = case (exprRelGenRelation expr, exprRelGenRelation exprr) of
                                                                          (Just (Cond rel), Just (Cond rell)) -> Just (Cond $ And rel rell)
                                                                          (Just v, Just vv) -> Just (Cond $ And (CBase $ BoolVar (display v)) (CBase $ BoolVar (display vv)))
                                                                          _ -> Just $ Other "ERROR"

  exprRelGenRelation (Binary "&&" expr exprr) = exprRelGenRelation (Binary "&" expr exprr)

  exprRelGenRelation (Binary "|" expr exprr) = case (exprRelGenRelation expr, exprRelGenRelation exprr) of
                                                                          (Just (Cond rel), Just (Cond rell)) -> Just (Cond $ Or rel rell)
                                                                          (Just v, Just vv) -> Just (Cond $ Or (CBase $ BoolVar (display v)) (CBase $ BoolVar (display vv)))
                                                                          v -> (Just $ Other "ERROR")

  exprRelGenRelation (Binary "||" expr exprr) = exprRelGenRelation (Binary "|" expr exprr)

  exprRelGenRelation (Binary ">" expr exprr) = case (exprRelGenRelation expr, exprRelGenRelation exprr) of
                                                                          (Just (Numb rel), Just (Numb rell)) -> Just (Cond $ Greater rel rell)
                                                                          (Just v, Just vv) -> Just (Cond $ Greater (NBase $ IntVar (display v)) (NBase $ IntVar (display vv)))
                                                                          _ -> Just $ Other "ERROR"


  exprRelGenRelation (Binary ">=" expr exprr) = case (exprRelGenRelation expr, exprRelGenRelation exprr) of
                                                                          (Just (Numb rel), Just (Numb rell)) -> Just (Cond $ GreaterOrEqual rel rell)
                                                                          (Just v, Just vv) -> Just (Cond $ GreaterOrEqual (NBase $ IntVar (display v)) (NBase $ IntVar (display vv)))
                                                                          _ -> Just $ Other "ERROR"


  exprRelGenRelation (Binary "<" expr exprr) = case (exprRelGenRelation expr, exprRelGenRelation exprr) of
                                                                          (Just (Numb rel), Just (Numb rell)) -> Just (Cond $ Less rel rell)
                                                                          (Just v, Just vv) -> Just (Cond $ Less (NBase $ IntVar (display v)) (NBase $ IntVar (display vv)))
                                                                          _ -> Just $ Other "ERROR"


  exprRelGenRelation (Binary "<=" expr exprr) = case (exprRelGenRelation expr, exprRelGenRelation exprr) of
                                                                          (Just (Numb rel), Just (Numb rell)) -> Just (Cond $ LessOrEqual rel rell)
                                                                          (Just v, Just vv) -> Just (Cond $ LessOrEqual (NBase $ IntVar (display v))  (NBase $ IntVar (display vv)))
                                                                          _ -> Just $ Other "ERROR"


  exprRelGenRelation (Binary "==" expr exprr) = (case (exprRelGenRelation expr, exprRelGenRelation exprr) of
                                                                                                    (Just rel, Just rell) -> Just (Cond $ Equals rel rell)
                                                                                                    (Just v, Just vv) -> Just (Cond $ Equals (Cond $ CBase $ BoolVar (display v)) (Cond $ CBase $ BoolVar (display vv)))
                                                                                                    _ -> Just $ Other "ERROR")

  exprRelGenRelation (Binary "!=" expr exprr) = case (exprRelGenRelation expr, exprRelGenRelation exprr) of
                                                                          (Just rel, Just rell) -> Just (Cond $ Not $ Equals rel rell)
                                                                          (Just v, Just vv) -> Just (Cond $ Not (Equals (Cond $ CBase $ BoolVar (display v)) (Cond $ CBase $ BoolVar (display vv))))
                                                                          v -> (Just $ Other "ERROR")

  exprRelGenRelation (MemberAccess expr (Identifier member)) = let maybeStructVal = exprRelGenRelation expr
                                                                   newMaybeGenRel = case maybeStructVal of
                                                                                                                --  Just (Other var) -> Just $ Structs $ (MemberSelect (StructBase $ StructVar var) member)
                                                                                          Just (Structs (MemberSelect (StructBase (StructVar var)) memberr)) -> Just $ Structs $ MemberSelect (MemberSelect (StructBase $ StructVar var) memberr) member
                                                                                          Just v -> Just $ Structs $ (MemberSelect (StructBase $ StructVar (display v)) member)
                                                                                          _ -> (Just $ Other "ERROR")
                                                                                    in newMaybeGenRel

  exprRelGenRelation _ = Nothing



--here deal with anything that can be represented as an assertrelation
--focus on changes to storage like assignment, delete (create a new version of the variable empty at the deleted index, or an empty map, see exact behaviour), storing
--TODO only generate new / next var if the var is used on the right-hand side
--TODO deal with delete
--TODO pre-parse the ternary operator into if-else clauses
--TODO difference betwee ++x; and x++; this depends on context, e.g. y = x++; and y' = ++x; will have different values. x++ rreturns the value of x then adds 1 to it, while ++x adds 1 to x and returns x
  exprRel :: Expression -> Maybe AssertRel

  exprRel (Unary "++" expr) = exprRel (Binary "=" expr (Binary "+" expr (Literal (PrimaryExpressionNumberLiteral (NumberLiteralDec "1" Nothing)))))
  exprRel (Unary "--" expr) = exprRel (Binary "=" expr (Binary "-" expr (Literal (PrimaryExpressionNumberLiteral (NumberLiteralDec "1" Nothing)))))

  exprRel (Binary "+=" lhs rhs) = exprRel (Binary "=" lhs (Binary "+" lhs rhs))
  exprRel (Binary "-=" lhs rhs) = exprRel (Binary "=" lhs (Binary "-" lhs rhs))
  exprRel (Binary "*=" lhs rhs) = exprRel (Binary "=" lhs (Binary "*" lhs rhs))
  exprRel (Binary "/=" lhs rhs) = exprRel (Binary "=" lhs (Binary "/" lhs rhs))
  exprRel (Binary "&=" lhs rhs) = exprRel (Binary "=" lhs (Binary "&" lhs rhs))
  exprRel (Binary "|=" lhs rhs) = exprRel (Binary "=" lhs (Binary "|" lhs rhs))
  exprRel (Binary "%=" lhs rhs) = exprRel (Binary "=" lhs (Binary "%" lhs rhs))

  exprRel (Binary "=" lhs rhs) = let maybeLHSGenRel = (exprRelGenRelation lhs)
                                     maybeRHSGenRel = (exprRelGenRelation rhs)
                                    in case (maybeLHSGenRel, maybeRHSGenRel) of
                                          (Nothing, _) -> Just $ ERROR
                                          (_, Nothing) -> Just $ ERROR
                                          (Just genRel, Just genRell) -> Just $ Assign genRel genRell

  exprRel expr = let maybeGenRel = exprRelGenRelation expr
                    in case maybeGenRel of
                          Nothing -> Nothing
                          Just (Cond rel) -> Just $ Rel rel
                          v -> Just ERROR

--TODO  exprRel sortDecs ssaContext (Unary "delete" expr) =

  exprRel _ = Nothing
