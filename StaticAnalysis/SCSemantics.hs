module StaticAnalysis.SCSemantics where

import CFG.CFG
import CFG.Parsing
import Solidity.Solidity
import qualified Data.List as List
import qualified DEA.DEA as DEA
import qualified StaticAnalysis.Residuals

import Data.Map.Strict
--import StaticAnalysis.Residuals

--type FunctionName = String

data Address = ProperAddress String
                | Pointer Expression 
                deriving (Eq, Ord, Show)

type Blockchain = Map Address SmartContract

data SmartContractKind = Contract | Interface | Library deriving (Eq, Ord, Show)

data Struct = Struct{
              structName :: Identifier,
              vars :: [VariableDeclaration]
            } deriving (Eq, Ord, Show)

data EnumType = EnumType{
              enumName :: Identifier,
              values :: [Identifier]
            } deriving (Eq, Ord, Show)

data Event = Event{
              eventName :: Identifier,
              indexedParameterList :: IndexedParameterList,
              anonymous :: Bool
            } deriving (Eq, Ord, Show)

data SmartContract = SmartContract{
                        kind :: SmartContractKind, --TODO inheritance
                        inherits :: [InheritanceSpecifier],
                        scName :: Identifier,
                        internalContracts :: [SmartContract], 
                        fields :: [StateVariableDeclaration],
                        structs :: [Struct],
                        enums :: [EnumType],
                        events :: [Event],
                        publicFunctions :: [FunctionCFG],
                        internalFunctions :: [FunctionCFG]--,
                        --callingTransitions :: [((State, String), Call)]
                    }
  deriving (Eq, Ord, Show)
           
type SC = SmartContract

type TypeSequence = [TypeName]
type Context = (FunctionCFG, SC, Blockchain)


codeToSemantics :: SolidityCode -> Maybe SC
codeToSemantics (SolidityCode (SourceUnit sourceUnits)) = let onlyContractDefinitions = [c | (SourceUnit1_ContractDefinition c) <- sourceUnits]
                                                              scs = List.map (contractDefinitionToSemantics) onlyContractDefinitions
                                                              properContracts = [sc | Just sc <- scs]
                                                            in if properContracts == []
                                                                then Nothing
                                                                else Just $ addInternalSCs (last properContracts) (removeLastSC properContracts)

addInternalSCs :: SC -> [SC] -> SC
addInternalSCs sc scs = SmartContract{
                        kind = kind sc,
                        inherits = inherits sc,
                        scName = scName sc,
                        internalContracts = scs,
                        fields = fields sc,
                        structs = structs sc,
                        enums = enums sc,
                        events = events sc,
                        publicFunctions = publicFunctions sc,
                        internalFunctions = internalFunctions sc
                    }

removeLastSC :: [SC] -> [SC]
removeLastSC [] = []
removeLastSC [sc] = []
removeLastSC (sc:scs) = (sc:(removeLastSC scs))

contractDefinitionToSemantics :: ContractDefinition -> Maybe SC
contractDefinitionToSemantics contractDefinition = case stringToSCKind (definitionType contractDefinition) of
                                                    Nothing -> Nothing
                                                    Just name -> let allFunctionCFGs = contractCFGFromContractDefinition contractDefinition
                                                                     publicFunctions = onlyExternallyVisibleFunctions allFunctionCFGs
                                                                  in 
                                                                    Just SmartContract{
                                                                        kind = name,
                                                                        inherits = isClause contractDefinition, --TODO identifierType needs to check these too?
                                                                        scName = definitionName contractDefinition, --TODO inheritance
                                                                        internalContracts = [],
                                                                        fields = fieldsFromContractParts (contractParts contractDefinition),
                                                                        structs = structsFromContractParts (contractParts contractDefinition),
                                                                        enums = enumsFromContractParts (contractParts contractDefinition),
                                                                        events = eventsFromContractParts (contractParts contractDefinition),
                                                                        publicFunctions = publicFunctions, 
                                                                        internalFunctions = allFunctionCFGs List.\\ publicFunctions
                                                                    }

eventsFromContractParts :: [ContractPart] -> [Event]
eventsFromContractParts [] = []
eventsFromContractParts ((ContractPartEventDefinition id indexedParameterList anon):cps) = ((Event id indexedParameterList anon):(eventsFromContractParts cps))
eventsFromContractParts (_:cps) = eventsFromContractParts cps

enumsFromContractParts :: [ContractPart] -> [EnumType]
enumsFromContractParts [] = []
enumsFromContractParts ((ContractPartEnumDefinition id enums):cps) = ((EnumType id enums):(enumsFromContractParts cps))
enumsFromContractParts (_:cps) = enumsFromContractParts cps


fieldsFromContractParts :: [ContractPart] -> [StateVariableDeclaration]
fieldsFromContractParts [] = []
fieldsFromContractParts ((ContractPartStateVariableDeclaration svd):cps) = (svd:(fieldsFromContractParts cps))
fieldsFromContractParts (_:cps) = fieldsFromContractParts cps

structsFromContractParts :: [ContractPart] -> [Struct]
structsFromContractParts [] = []
structsFromContractParts ((ContractPartStructDefinition id varDecList):cps) = ((Struct id varDecList):(structsFromContractParts cps))
structsFromContractParts (_:cps) = structsFromContractParts cps

onlyExternallyVisibleFunctions :: [FunctionCFG] -> [FunctionCFG]
onlyExternallyVisibleFunctions [] = []
onlyExternallyVisibleFunctions (f:fs) = case (functionVisibility (signature f)) of
                                          Just Public -> (f:(onlyExternallyVisibleFunctions fs))
                                          Just FExternal -> (f:(onlyExternallyVisibleFunctions fs))
                                          _ -> (onlyExternallyVisibleFunctions fs)

stringToSCKind :: String -> Maybe SmartContractKind
stringToSCKind "contract" = Just Contract
stringToSCKind "library" = Just Library
stringToSCKind "interface" = Just Interface
stringToSCKind _ = Nothing

primaryExpressionMatchesType :: PrimaryExpression -> TypeSequence -> Context -> Bool

primaryExpressionMatchesType (PrimaryExpressionBooleanLiteral _) [typeName] _ = case typeName of
                                                                                 TypeNameElementaryTypeName BoolType -> True
                                                                                 TypeNameElementaryTypeName VarType -> True
                                                                                 _ -> False
                                                                                
primaryExpressionMatchesType (PrimaryExpressionNumberLiteral _) [typeName] _ = case typeName of
                                                                                 TypeNameElementaryTypeName AddressType -> True
                                                                                 TypeNameElementaryTypeName (IntType _) -> True
                                                                                 TypeNameElementaryTypeName (UintType _) -> True
                                                                                 TypeNameElementaryTypeName (UfixedType _) -> True
                                                                                 TypeNameElementaryTypeName (FixedType _) -> True
                                                                                 TypeNameElementaryTypeName (VarType) -> True
                                                                                 _ -> False
primaryExpressionMatchesType (PrimaryExpressionHexLiteral _) [typeName] _ = case typeName of
                                                                                 TypeNameElementaryTypeName AddressType -> True
                                                                                 TypeNameElementaryTypeName (IntType _) -> True
                                                                                 TypeNameElementaryTypeName (UintType _) -> True
                                                                                 TypeNameElementaryTypeName (UfixedType _) -> True
                                                                                 TypeNameElementaryTypeName (FixedType _) -> True
                                                                                 TypeNameElementaryTypeName (VarType) -> True
                                                                                 _ -> False
primaryExpressionMatchesType (PrimaryExpressionStringLiteral _) [typeName] _ = case typeName of
                                                                                 TypeNameElementaryTypeName StringType -> True
                                                                                 TypeNameElementaryTypeName VarType -> True
                                                                                 _ -> False
primaryExpressionMatchesType (PrimaryExpressionTupleExpression (RoundBrackets expressionList)) typeNames context = if length expressionList /= length typeNames
                                                                                                                then False
                                                                                                                else f expressionList typeNames
                                                                                                              where 
                                                                                                                f [] [] = True
                                                                                                                f (e:es) (t:ts) = (expressionMatchesType e [t] context) && (f es ts)

primaryExpressionMatchesType (PrimaryExpressionTupleExpression (SquareBrackets expressionList)) typeNames context = primaryExpressionMatchesType (PrimaryExpressionTupleExpression (RoundBrackets expressionList)) typeNames context

primaryExpressionMatchesType (PrimaryExpressionIdentifier id) [typeName] (cfg,sc,bc) = case identifierType id (Just cfg) sc of
                                                                                          Nothing -> False
                                                                                          Just typee -> typeName == typee

primaryExpressionMatchesType (PrimaryExpressionElementaryTypeNameExpression elementaryType1) [(TypeNameElementaryTypeName elementaryType2)] _ = elementaryType1 == elementaryType2 --is this correct?

primaryExpressionMatchesType _ _ _ = False


expressionToFunctionCall :: Expression -> Maybe FunctionCall
expressionToFunctionCall (FunctionCallExpressionList (Literal (PrimaryExpressionIdentifier functionID)) Nothing) = Just (FunctionCall functionID Nothing)
expressionToFunctionCall (FunctionCallExpressionList (Literal (PrimaryExpressionIdentifier functionID)) (Just expressionList)) = Just (FunctionCall functionID (Just (Right expressionList)))
expressionToFunctionCall (FunctionCallNameValueList (Literal (PrimaryExpressionIdentifier functionID)) Nothing) = Just (FunctionCall functionID Nothing)
expressionToFunctionCall (FunctionCallNameValueList (Literal (PrimaryExpressionIdentifier functionID)) (Just nameValueList)) = Just (FunctionCall functionID (Just (Left nameValueList)))

expressionToFunctionCall (FunctionCallExpressionList (MemberAccess exp functionID) Nothing) = Just (OutsideFunctionCall exp functionID Nothing)
expressionToFunctionCall (FunctionCallExpressionList (MemberAccess exp functionID) (Just expressionList)) = Just (OutsideFunctionCall exp functionID (Just (Right expressionList)))
expressionToFunctionCall (FunctionCallNameValueList (MemberAccess exp functionID) Nothing) = Just (OutsideFunctionCall exp functionID Nothing)
expressionToFunctionCall (FunctionCallNameValueList (MemberAccess exp functionID) (Just nameValueList)) = Just (OutsideFunctionCall exp functionID (Just (Left nameValueList)))


expressionMatchesType :: Expression -> [TypeName] -> Context -> Bool
expressionMatchesType (Unary "delete" _) _ _ =False
expressionMatchesType (Unary _ expression) typenames context = expressionMatchesType expression typenames context
expressionMatchesType (Binary "[]" (Literal (PrimaryExpressionIdentifier arrayID)) _) [typename] (cfg, sc, _) = let typeOfArray = identifierType arrayID (Just cfg) sc
                                                                                                              in case typeOfArray of
                                                                                                                  Just (TypeNameArrayTypeName typename _) -> True
                                                                                                                  _ -> False
expressionMatchesType (Binary "[]" (Ternary "?" _ expression2 expression3) expression4) typenames context = expressionMatchesType (Binary "[]"  expression2 expression4) typenames context ||  expressionMatchesType (Binary "[]"  expression3 expression4) typenames context
expressionMatchesType (Binary _ expression1 expression2) typenames context = expressionMatchesType expression1 typenames context || expressionMatchesType expression2 typenames context
expressionMatchesType (Ternary "?" _ expression2 expression3) typenames context = expressionMatchesType expression2 typenames context || expressionMatchesType expression3 typenames context

--FunctionCall = FunctionCall FunctionName (Maybe (Either NameValueList ExpressionList)) 


{-
gasleft() returns (uint256): remaining gas
block.blockhash(uint blockNumber) returns (bytes32): hash of the given block - only works for 256 most recent blocks excluding current
<address>.transfer(uint256 amount):
send given amount of Wei to Address, throws on failure, forwards 2300 gas stipend, not adjustable
<address>.send(uint256 amount) returns (bool):
send given amount of Wei to Address, returns false on failure, forwards 2300 gas stipend, not adjustable
<address>.call(...) returns (bool):
issue low-level CALL, returns false on failure, forwards all available gas, adjustable
<address>.callcode(...) returns (bool):
issue low-level CALLCODE, returns false on failure, forwards all available gas, adjustable
<address>.delegatecall(...) returns (bool):
issue low-level DELEGATECALL, returns false on failure, forwards all available gas, adjustable
now (uint): current block timestamp (alias for block.timestamp)

-}

--expressionMatchesType (FunctionCallNameValueList (Literal (PrimaryExpressionIdentifier functionName)) (maybeNameValueList)) typeName context =

--expressionMatchesType (FunctionCallNameValueList (MemberAccess expression functionName) (Maybe NameValueList)) typeName context =

--expressionMatchesType (FunctionCallExpressionList (Literal (PrimaryExpressionIdentifier functionName)) (Maybe ExpressionList)) typeName context =



expressionMatchesType (TypeCasting elementaryTypeName expression) [typeName] _ = (TypeNameElementaryTypeName elementaryTypeName) == typeName

--msg.sender (address): sender of the message (current call)
expressionMatchesType (MemberAccess (Literal (PrimaryExpressionIdentifier (Identifier "block"))) (Identifier"coinbase")) [(TypeNameElementaryTypeName AddressType)] _ = True
expressionMatchesType (MemberAccess (Literal (PrimaryExpressionIdentifier (Identifier "block"))) (Identifier"difficulty")) [(TypeNameElementaryTypeName (UintType Nothing))] _ = True
expressionMatchesType (MemberAccess (Literal (PrimaryExpressionIdentifier (Identifier "block"))) (Identifier"gaslimit")) [(TypeNameElementaryTypeName (UintType Nothing))] _ = True
expressionMatchesType (MemberAccess (Literal (PrimaryExpressionIdentifier (Identifier "block"))) (Identifier"number")) [(TypeNameElementaryTypeName (UintType Nothing))] _ = True
expressionMatchesType (MemberAccess (Literal (PrimaryExpressionIdentifier (Identifier "block"))) (Identifier"timestamp")) [(TypeNameElementaryTypeName (UintType Nothing))] _ = True
expressionMatchesType (MemberAccess (Literal (PrimaryExpressionIdentifier (Identifier "block"))) (Identifier"difficulty")) [(TypeNameElementaryTypeName (UintType (Just 256)))] _ = True
expressionMatchesType (MemberAccess (Literal (PrimaryExpressionIdentifier (Identifier "block"))) (Identifier"gaslimit")) [(TypeNameElementaryTypeName (UintType (Just 256)))] _ = True
expressionMatchesType (MemberAccess (Literal (PrimaryExpressionIdentifier (Identifier "block"))) (Identifier"number")) [(TypeNameElementaryTypeName (UintType (Just 256)))] _ = True
expressionMatchesType (MemberAccess (Literal (PrimaryExpressionIdentifier (Identifier "block"))) (Identifier"timestamp")) [(TypeNameElementaryTypeName (UintType (Just 256)))] _ = True
expressionMatchesType (MemberAccess (Literal (PrimaryExpressionIdentifier (Identifier "msg"))) (Identifier"sender")) [(TypeNameElementaryTypeName AddressType)] _ = True
expressionMatchesType (MemberAccess (Literal (PrimaryExpressionIdentifier (Identifier "msg"))) (Identifier"gas")) [(TypeNameElementaryTypeName (UintType Nothing))] _ = True
expressionMatchesType (MemberAccess (Literal (PrimaryExpressionIdentifier (Identifier "msg"))) (Identifier"gas")) [(TypeNameElementaryTypeName (UintType (Just 256)))] _ = True
expressionMatchesType (MemberAccess (Literal (PrimaryExpressionIdentifier (Identifier "msg"))) (Identifier"data")) [(TypeNameElementaryTypeName (BytesType Nothing))] _ = True
expressionMatchesType (MemberAccess (Literal (PrimaryExpressionIdentifier (Identifier "msg"))) (Identifier"sig")) [(TypeNameElementaryTypeName (BytesType (Just 4)))] _ = True
expressionMatchesType (MemberAccess (Literal (PrimaryExpressionIdentifier (Identifier "msg"))) (Identifier"value")) [(TypeNameElementaryTypeName (UintType Nothing))] _ = True
expressionMatchesType (MemberAccess (Literal (PrimaryExpressionIdentifier (Identifier "msg"))) (Identifier"value")) [(TypeNameElementaryTypeName (UintType (Just 256)))] _ = True
expressionMatchesType (MemberAccess (Literal (PrimaryExpressionIdentifier (Identifier "tx"))) (Identifier"gasprice")) [(TypeNameElementaryTypeName (UintType Nothing))] _ = True
expressionMatchesType (MemberAccess (Literal (PrimaryExpressionIdentifier (Identifier "tx"))) (Identifier"gasprice")) [(TypeNameElementaryTypeName (UintType (Just 256)))] _ = True
expressionMatchesType (MemberAccess (Literal (PrimaryExpressionIdentifier (Identifier "tx"))) (Identifier"origin")) [(TypeNameElementaryTypeName AddressType)] _ = True



expressionMatchesType (MemberAccess (Ternary "?" _ exp2 exp3) (Identifier fieldIdName)) [typeName] context = expressionMatchesType (MemberAccess exp2 (Identifier fieldIdName)) [typeName] context && expressionMatchesType (MemberAccess exp3 (Identifier fieldIdName)) [typeName] context

--TODO
expressionMatchesType (MemberAccess exp (Identifier fieldIdName)) [typeName] (cfg, sc, bc) = case identifierTypeFromMemberAccess (MemberAccess exp (Identifier fieldIdName)) (cfg, sc, bc) of
                                                                                                Nothing -> False
                                                                                                Just id -> typeName == id --TODO, is this the full behaviou?


--todo not finished below

expressionMatchesType (Literal primaryExpression) typeName context = primaryExpressionMatchesType primaryExpression typeName context
expressionMatchesType (New typeName1) [typeName2] _ = typeName1 == typeName2


expressionMatchesType exps typeNames (callerCFG, sc, blockchain) = case expressionToFunctionCall exps of
                                                                      Nothing -> False
                                                                      Just functionCall -> let maybeCalledFunctionCFG = functionCallToCFG functionCall (callerCFG, sc, blockchain)
                                                                                              in case maybeCalledFunctionCFG of
                                                                                                  Just calledFunctionCFG ->  let returnParamss = returnParams (signature calledFunctionCFG)
                                                                                                                                 returnTypes = listType returnParamss
                                                                                                                                in returnTypes == typeNames
                                                                                                  Nothing -> if length typeNames == 1
                                                                                                              then case exps of
                                                                                                                      (Literal (PrimaryExpressionIdentifier (Identifier "addmod"))) -> head typeNames == TypeNameElementaryTypeName (UintType Nothing) || head typeNames == TypeNameElementaryTypeName (UintType (Just 256))
                                                                                                                      (Literal (PrimaryExpressionIdentifier (Identifier "mulmod"))) -> head typeNames == TypeNameElementaryTypeName (UintType (Just 256)) || head typeNames == TypeNameElementaryTypeName (UintType Nothing)
                                                                                                                      (Literal (PrimaryExpressionIdentifier (Identifier "keccak256"))) -> head typeNames == TypeNameElementaryTypeName (BytesType (Just 32))
                                                                                                                      (Literal (PrimaryExpressionIdentifier (Identifier "sha256"))) -> head typeNames == TypeNameElementaryTypeName (BytesType (Just 32))
                                                                                                                      (Literal (PrimaryExpressionIdentifier (Identifier "sha3"))) -> head typeNames == TypeNameElementaryTypeName (BytesType (Just 32))
                                                                                                                      (Literal (PrimaryExpressionIdentifier (Identifier "ripemd160"))) -> head typeNames == TypeNameElementaryTypeName (BytesType (Just 20))
                                                                                                                      (Literal (PrimaryExpressionIdentifier (Identifier "ecrecover"))) -> head typeNames == TypeNameElementaryTypeName AddressType
                                                                                                                      _ -> False
                                                                                                              else False
                                                                          where
                                                                             listType (ParameterList []) = []
                                                                             listType (ParameterList (p:ps)) = (parameterType p:(listType (ParameterList ps)))


{-
this (current contract’s type):
the current contract, explicitly convertible to Address
-}


isArrayType :: Maybe TypeName -> Bool
isArrayType (Just (TypeNameArrayTypeName _ _)) = True
isArrayType _ = False

isUserDefined :: Maybe TypeName -> Bool
isUserDefined (Just (TypeNameUserDefinedTypeName _)) = True
isUserDefined _ = False

typeOfVariableInStruct :: [Identifier] -> Identifier -> SC -> Maybe TypeName
typeOfVariableInStruct [] _ _ = Nothing
typeOfVariableInStruct (structId:[]) varId sc = let matchingStructs = [s | s <- structs sc, structName s == structId]
                                                   in if matchingStructs == []
                                                       then Nothing
                                                       else let matchingVarsTypes = [variableDeclarationType var | var <- vars (head matchingStructs), variableDeclarationName var == varId]
                                                              in if matchingVarsTypes == []
                                                                  then Nothing
                                                                  else Just (head matchingVarsTypes)
typeOfVariableInStruct (scId:ids) varId sc = if scId == scName sc 
                                                          then if length ids > 1 
                                                                  then Nothing
                                                                  else typeOfVariableInStruct ids varId sc
                                                          else let matchingSCs = [s | s <- internalContracts sc, scName s == scId]
                                                                in if matchingSCs == []
                                                                    then Nothing
                                                                    else typeOfVariableInStruct ids varId (head matchingSCs)


----TODO doesn t take care of function overloaded but with same name parameters e.g. f(int i), f(string i)
--matchesParameterList :: (Either NameValueList ExpressionList) -> ParameterList -> Bool
--matchesParameterList Left (NameValueList identifierExpressionList) (ParameterList parameterTypeList) = 
--                                                    let matches = [id | (id, _) <- identifierExpressionList, (Parameter _ id) <- parameterTypeList]
--                                                        in (length matches) == (length identifierExpressionList)
--                                                         && (length matches) == (length parameterTypeList)
--matchesParameterList Right (ExpressionList identifierExpressionList) (ParameterList parameterTypeList) = 
--                                                    let matches = [id | (id, _) <- identifierExpressionList, (Parameter _ id) <- parameterTypeList]
--                                                        in (length matches) == (length identifierExpressionList)
--                                                        && (length matches) == (length parameterTypeList)
                


--TODO handle var type

--expressionMatchesType (MemberAccess (MemberAccess exp) (Identifier fieldIdName)) [typeName] (cfg, sc, bc) = let structPointerType = identifierType pointer cfg sc
--                                                                                                              in 
--                                                                     where
--                                                                      structType (MemberAccess (Literal (PrimaryExpressionIdentifier pointer)) (Identifier fieldIdName)) = 

--expressionMatchesType (MemberAccess (Literal (PrimaryExpressionIdentifier pointer)) (Identifier fieldIdName)) [typeName] (cfg, sc, bc) = 
--                                                                         let structPointerType = identifierType pointer cfg sc

contractTypeOfIdentifier :: Identifier -> [SC] -> Maybe SC
contractTypeOfIdentifier _ [] = Nothing
contractTypeOfIdentifier contractName (sc:scs) = if (scName sc) == contractName
                                                  then Just sc
                                                  else contractTypeOfIdentifier contractName scs

structTypeOfIdentifier :: Identifier -> [Struct] -> Maybe Struct
structTypeOfIdentifier id [] = Nothing
structTypeOfIdentifier id (st:sts) = if id == (structName st)
                                        then (Just st)
                                        else structTypeOfIdentifier id sts


typeOfIdentifierInStruct :: Identifier -> Struct -> Maybe TypeName
typeOfIdentifierInStruct id struct = let matchingVarTypes = [variableDeclarationType v | v <- vars struct, id == (variableDeclarationName v)]
                                        in if length matchingVarTypes == 0 --TODO maybe =/= 1 better
                                             then Nothing
                                             else Just (head matchingVarTypes)


typeOfIdentifierInContract :: Identifier -> SC -> Maybe TypeName
typeOfIdentifierInContract id sc = let matchingFields = [typename f | f <- fields sc, id == (variableName f)]
                                    in if length matchingFields == 0
                                         then Nothing
                                         else Just (head matchingFields)

identifierTypeInContractOrStruct :: Identifier -> Maybe TypeName -> SC -> Maybe TypeName
identifierTypeInContractOrStruct varId contractOrStructType sc = case contractOrStructType of
                                                                  --id is a contract or struct type, e.g. GStruct {int i;} is a struct, and we have Gstruct j; <<<j.i;>>>
                                                                  Just (TypeNameUserDefinedTypeName (UserDefinedTypeName [id])) -> let maybeContract = contractTypeOfIdentifier id [sc]
                                                                                                                                        in case maybeContract of
                                                                                                                                              Nothing -> let maybeStruct = structTypeOfIdentifier id (structs sc)
                                                                                                                                                            in case maybeStruct of
                                                                                                                                                                  Nothing -> Nothing
                                                                                                                                                                  Just struct -> typeOfIdentifierInStruct varId struct
                                                                                                                                              Just contract -> typeOfIdentifierInContract varId contract
                                                                  --id is a contract type, id" is a struct type
                                                                  Just (TypeNameUserDefinedTypeName (UserDefinedTypeName (id:[id']))) -> let maybeContract = contractTypeOfIdentifier id ([sc] ++ (internalContracts sc))
                                                                                                                                          in case maybeContract of
                                                                                                                                                Nothing -> Nothing
                                                                                                                                                Just contract -> let maybeStruct = structTypeOfIdentifier id' (structs contract)
                                                                                                                                                                    in case maybeStruct of
                                                                                                                                                                          Nothing -> Nothing
                                                                                                                                                                          Just struct -> typeOfIdentifierInStruct varId struct
                                                                  _ -> Nothing --impossible, only 2 levels deep possible, e.g. SC.Struct types


identifierTypeFromMemberAccess :: Expression -> Context -> Maybe TypeName

identifierTypeFromMemberAccess (MemberAccess (Literal (PrimaryExpressionIdentifier pointer)) (Identifier varId)) (cfg, sc, bc) = let idType = identifierType pointer (Just cfg) sc
                                                                                                                                          in identifierTypeInContractOrStruct (Identifier varId) idType sc

identifierTypeFromMemberAccess (MemberAccess 
                                  (MemberAccess (Literal (PrimaryExpressionIdentifier pointer)) (Identifier varId1))
                              (Identifier varId2)) (cfg, sc, bc) = let contractOrStructType = identifierTypeFromMemberAccess (MemberAccess (Literal (PrimaryExpressionIdentifier pointer)) (Identifier varId1)) (cfg, sc, bc)
                                                                      in identifierTypeInContractOrStruct (Identifier varId2) contractOrStructType sc

identifierTypeFromMemberAccess (MemberAccess 
                                  expression
                              (Identifier varId)) (cfg, sc, bc) = let contractOrStructType = identifierTypeFromMemberAccess expression (cfg, sc, bc)
                                                                      in identifierTypeInContractOrStruct (Identifier varId) contractOrStructType sc

--TODO consider having a function call as the first argument of member access, but currently this is only experimental behaviour in Solidity, it is not possible by default for a function to return a Struct
identifierTypeFromMemberAccess expression _ = Nothing

--data Struct = Struct{
--              structName :: Identifier,
--              vars :: [VariableDeclaration]
--            } deriving (Eq, Ord, Show)

identifierTypeFromStatements :: Identifier -> [Statement] -> Maybe TypeName
identifierTypeFromStatements _ [] = Nothing
identifierTypeFromStatements id ((SimpleStatementVariableDeclaration decl maybeExp):ss) = if variableDeclarationName decl == id
                                                                                          then Just (variableDeclarationType decl)
                                                                                          else identifierTypeFromStatements id ss

identifierType :: Identifier -> Maybe FunctionCFG -> SC -> Maybe TypeName
identifierType id (Just cfg) sc = let cfgStatements = [st | (Transition _ _ (Label st)) <- transitions cfg]
                                      identifierTypee = identifierTypeFromStatements id cfgStatements
                                     in if identifierTypee == Nothing
                                           then let cfgSignature = signature cfg
                                                    allParameters = (unpackParameterList $ parameters cfgSignature) ++ (unpackParameterList $ returnParams cfgSignature)
                                                    matchingParamaters = [param | param <- allParameters, parameterIdentifier param == Just id]
                                                  in if length matchingParamaters == 0
                                                      then identifierType id Nothing sc
                                                      else Just (parameterType (head matchingParamaters))
                                           else Nothing
                                           where 
                                              unpackParameterList (ParameterList list) = list
identifierType id (Nothing) sc = let scFields = fields sc
                                     matchingParamaters = [param | param <- fields sc, variableName param == id]
                                      in if length matchingParamaters == 0
                                          then Nothing
                                          else Just (typename (head matchingParamaters))
            
--TODO delegateCalls, calls along with revert, assert, require                 
--FunctionCall = FunctionCall FunctionName (Maybe (Either NameValueList ExpressionList))
functionCallToCFG :: FunctionCall -> Context -> Maybe FunctionCFG
functionCallToCFG (FunctionCall functionName values) (f, sc, bc) = let functionsWithName = [f | f <- publicFunctions sc]
                                                                    in if functionsWithName == []
                                                                         then Nothing
                                                                          else case values of
                                                                          Nothing -> returnFirstOrNothing [f | f <- functionsWithName, (ParameterList []) == (parameters (signature f))]
                                                                          Just (Left (NameValueList idExpList)) -> returnFirstOrNothing [ff | ff <- functionsWithName, nameValueListMatchesParameters idExpList (parameters (signature ff)) (f, sc, bc)]
                                                                          Just (Right (ExpressionList exps)) -> returnFirstOrNothing [ff | ff <- functionsWithName, expressionListMatchesParameters exps (parameters (signature ff)) (f, sc, bc)]

--todo Outside functioncall

--newtype ParameterList = ParameterList [Parameter] deriving (Eq, Ord, Show)
--newtype NameValueList = NameValueList [(Identifier, Expression)] deriving (Show, Eq, Ord)
--newtype ExpressionList = ExpressionList { unExpressionList :: [Expression] } deriving (Eq, Ord, Show)


nameValueListMatchesParameters :: [(Identifier, Expression)] -> ParameterList-> Context -> Bool
nameValueListMatchesParameters tuples (ParameterList params) context =  let parameterTypeExpressionCouple = [(parameterType p, exp) | p <- params, (id, exp) <- tuples, parameterIdentifier p == Just id] 
                                                                                         in if length parameterTypeExpressionCouple /= length params
                                                                                              then False
                                                                                              else if [(t, exp) | (t, exp) <- parameterTypeExpressionCouple, not (expressionMatchesType exp [t] context)] /= []
                                                                                                    then False
                                                                                                    else True

expressionListMatchesParameters :: [Expression] -> ParameterList -> Context -> Bool
expressionListMatchesParameters [] (ParameterList []) context = True
expressionListMatchesParameters (e:exps) (ParameterList (p:params)) context =  let t = parameterType p
                                                                               in if expressionMatchesType e [t] context
                                                                                    then expressionListMatchesParameters exps (ParameterList params) context
                                                                                    else False

returnFirstOrNothing :: [a] -> Maybe a
returnFirstOrNothing [] = Nothing
returnFirstOrNothing (a:as) = Just a


type AbstractionFunction a = (Transition, Context) -> a -> a

type AF a = AbstractionFunction a

type SCState = (State, Context)

type EndCondition a = ([SCState]) -> a -> Bool

type Join a = [a] -> a

type DEAState = ([DEA.State], DEA.DEA)

deaAF :: AbstractionFunction DEAState
deaAF (t, (f, sc, _)) (states, dea) = let nextStates = [next | s <- states, next <- StaticAnalysis.Residuals.transitionDEAWithCFGTransition dea s t]
                                       in (nextStates, dea)



--TODO DEAL WITH DELEGATE CALLS CHANGING STATE
faOneStep :: SCState -> AF a -> EndCondition a -> Join a -> a -> a

--OutsideFunctionCall Expression FunctionName (Maybe (Either NameValueList ExpressionList))

--faOneStep ((OutsideFunctionCall exp l ff),(f,sc,bc)) af end join conca = 
--                                         let maybeffCFG = functionCallToCFG ff (f, sc, bc) 
--                                           in case maybeffCFG of
--                                                  Nothing -> conca
--                                                  Just ffCFG -> let aAfterCall = faOneFunction [(initial ffCFG, (ffCFG,sc,bc))] af end join conca
--                                                                    transitionsAfter = [t | t <- transitions f, (src t) == (FunctionCallState l ff)]
--                                                                 in join [af (t, (f,sc,bc)) aAfterCall | t <- transitionsAfter]

faOneStep ((FunctionCallState l ff),(f,sc,bc)) af end join conca = 
                                         let maybeffCFG = functionCallToCFG ff (f, sc, bc) 
                                           in case maybeffCFG of
                                                  Nothing -> conca
                                                  Just ffCFG -> let aAfterCall = faOneFunction [(initial ffCFG, (ffCFG,sc,bc))] af end join conca
                                                                    transitionsAfter = [t | t <- transitions f, (src t) == (FunctionCallState l ff)]
                                                                 in join [af (t, (f,sc,bc)) aAfterCall | t <- transitionsAfter]

faOneStep (s,(f,sc,bc)) af end join conca = let transitionsAfter = [t | t <- transitions f, (src t) == s]
                                             in join [af (t,(f,sc,bc)) conca | t <- transitionsAfter]

faOneFunction :: [SCState] -> AF a -> EndCondition a -> Join a -> a -> a
faOneFunction ((s,(f,sc,bc)):rest) af end join conca = let nextStates = statesAfter f [s]
                                                           nexta = faOneStep (s,(f,sc,bc)) af end join conca
                                                           nextSCStates = [(nexts,(f,sc,bc)) | nexts <- nextStates]
                                                          in if end nextSCStates nexta
                                                                then nexta
                                                                else faOneFunction (nextSCStates ++ rest) af end join nexta
                                                                    
forwardAnalysis :: SC -> Blockchain -> AF a -> EndCondition a -> Join a -> a -> a
forwardAnalysis sc bc af end join conca = let initStates = [(initial f, (f,sc,bc)) | f <- publicFunctions sc]
                                              nexta = faOneFunction initStates af end join conca
                                              in if end initStates nexta
                                                   then nexta
                                                   else forwardAnalysis sc bc af end join nexta

    
andthen :: FunctionCFG -> FunctionCFG -> FunctionCFG
f `andthen` g = let nonThrowingF = (prependStateLabelsWith "f" (nonThrowingBehaviour f))
                    nonThrowingG = (prependStateLabelsWith "g" (nonThrowingBehaviour g))
                    endState = BasicState "end"
                    fSignature = signature f
                    gSignature = signature g
                 in FunctionCFG{
                        signature = FunctionSignature{
                                        functionName = Identifier ("(" ++ (display fSignature) ++ ");(" ++ (display gSignature) ++ ")"),
                                        functionVisibility = Nothing, --irrelevant here
                                        parameters = ParameterList [], --TODO how to handle?
                                        returnParams = ParameterList [] --TODO how to handle?
                                    },
                        transitions = (transitions nonThrowingF) 
                                   ++ (transitions nonThrowingG)
                                   ++ [Transition (initial nonThrowingF) (initial nonThrowingG) Tau]
                                   ++ [Transition s (initial nonThrowingG) Tau | s <- (end nonThrowingF)]
                                   ++ [Transition s endState Tau | s <- (end nonThrowingG)]
                                   ++ [Transition (initial nonThrowingG) endState Tau],
                        states = (states nonThrowingF) ++ (states nonThrowingG) ++ [endState],
                        initial = initial nonThrowingF,
                        end = [endState]
                    }

throwingBehaviour :: FunctionCFG -> FunctionCFG
throwingBehaviour cfg = keepOnlyTillStates cfg [ThrowState, RevertState]


nonThrowingBehaviour :: FunctionCFG -> FunctionCFG
nonThrowingBehaviour cfg = keepOnlyTillStates cfg (end cfg)
                        
                        
keepOnlyTillStates :: FunctionCFG -> [State] -> FunctionCFG
keepOnlyTillStates cfg endStates = let newStates = [s | s <- (states cfg), s' <- endStates, s' <- (statesAfter cfg [s'])]
                                    in FunctionCFG{
                                          signature = signature cfg,
                                          transitions = [t | t <- transitions cfg, elem (src t) newStates, elem (dst t) newStates],
                                          states = newStates,
                                          initial = initial cfg,
                                          end = (end cfg) List.\\ endStates
                                      }
                        
                        
pathBetween :: FunctionCFG -> State -> State -> Bool
pathBetween cfg q q' = elem q' (statesAfter cfg [q])

statesAfter :: FunctionCFG -> [State] -> [State]
statesAfter cfg [] = []
statesAfter cfg states = let afterOneStep = oneStep cfg states
                             in if((afterOneStep List.\\ states) /= [])
                                    then statesAfter cfg afterOneStep
                                    else states
                                    
oneStep :: FunctionCFG -> [State] -> [State]
oneStep cfg states = [dst | src <- states, Transition src dst _ <- transitions cfg]
