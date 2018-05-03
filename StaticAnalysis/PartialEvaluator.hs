module StaticAnalysis.PartialEvaluator where
 import Data.Map.Strict as Map
 -- import CFG.CFG
 import Data.ByteString
 import Data.Either
 import qualified Solidity.Solidity as Solidity
  --hiding (UIntType, IntType, AddressType, BoolType, StringType, BytesType, ByteType, FixedType, UfixedType)
 import CFG.CFG
 import Data.Text.Lazy.Read
 import Data.Text.Lazy

 data UnknownOrValue a = Unknown --TODO update to include invariants
                        | V a deriving (Show, Eq, Ord)

 --TODO different sizes of Bytes (e.g. bytes4) and integer
 data Value = AddressType (UnknownOrValue Integer) --20 bytes
                | BoolType (UnknownOrValue Bool)
                | StringType (UnknownOrValue String)
                | IntType (UnknownOrValue Integer)
                | UIntType (UnknownOrValue Integer)
                | BytesType (UnknownOrValue [Integer])
                | ByteType (UnknownOrValue Integer)
                | FixedType (UnknownOrValue (Integer, Integer))
                | UfixedType (UnknownOrValue (Integer, Integer))
                | Tuple [PartialExpression]
                | Untyped String
                | NewContract String Integer -- integer represents contract add
               --TODO
               -- | Array [Value]
               -- | Struct [(Identifier, Value)]
                deriving (Show, Eq, Ord)
                
  --data PartialValue a = Known a | Unknown
  

 -- data UnknownOrValue a = Error | Unknown | Expression | V a deriving (Show, Eq, Ord)
  
  --data ErrorOrPartialExpression = Error | Val Value | Expression deriving (Show, Eq, Ord)
  
--  type BasicNumber = IntNum Integer | Hex String
--  data Number = Wei BasicNumber
--                    | Szabo BasicNumber
--                    | Finney BasicNumber
--                    | Ether BasicNumber
--                    | Seconds BasicNumber
--                    | Minutes BasicNumber
--                    | Hours BasicNumber
--                    | Days BasicNumber
--                    | Weeks BasicNumber
--                    | Years BasicNumber
--                    | Basic BasicNumber
  
--  data BasicValue = Str String 
--                    | No Number
--                    | B Bool
--                    | T [BasicValue]
    
 data Symbol = Sym String deriving (Show, Eq, Ord)
 data PartialExpression = Error 
                        | Val Value
                        | Unary String PartialExpression
                        | Binary String PartialExpression PartialExpression
                        | Ternary String PartialExpression PartialExpression PartialExpression
                        | FunctionCallNameValueList PartialExpression (Maybe [(Symbol, PartialExpression)])
                        | FunctionCallExpressionList PartialExpression (Maybe [PartialExpression])
                        | TypeCasting Solidity.ElementaryTypeName PartialExpression
                        | MemberAccess PartialExpression Symbol
                        | Literal Value
                        | Id Symbol
                        deriving (Show, Eq, Ord)

 type ProgramState = (Storage, Memory, Bool) 
  
 type Storage = Map Symbol PartialExpression
 type Memory = Map Symbol PartialExpression
--  type Stack = Map Expression PartialExpression
 
 ----------------------------------
 --Util Functions
 ----------------------------------
 

 
 getValueOf :: ProgramState -> Symbol -> PartialExpression
 getValueOf (storage, memory, _) id =  case (Map.lookup id memory) of
                                         Just mmrVal -> mmrVal
                                         Nothing -> case (Map.lookup id storage) of
                                                      Just strVal -> strVal
                                                      Nothing -> Error
 
 push :: ProgramState -> Symbol -> PartialExpression -> ProgramState
 push (storage, memory, error) id exp = case Map.lookup id memory of
                                          Just mmrVal -> (storage, insert id exp memory, error)
                                          Nothing -> case Map.lookup id storage of
                                                       Just strVal -> (storage, insert id exp memory, error)
                                                       Nothing -> (storage, memory, True)
     
 expressionToPartialExpression :: Solidity.Expression -> PartialExpression
 expressionToPartialExpression (Solidity.Unary string expression) = (Unary string (expressionToPartialExpression expression))
 
 expressionToPartialExpression (Solidity.Binary string expression1 expression2) = (Binary string (expressionToPartialExpression expression1) (expressionToPartialExpression expression2))
 
 expressionToPartialExpression (Solidity.Ternary string expression1 expression2 expression3) = (Ternary string (expressionToPartialExpression expression1) (expressionToPartialExpression expression2) (expressionToPartialExpression expression3))
 
 expressionToPartialExpression (Solidity.FunctionCallNameValueList expression Nothing) = (FunctionCallNameValueList (expressionToPartialExpression expression) Nothing)

-- newtype NameValueList = NameValueList [(Identifier, Expression)] deriving (Show, Eq, Ord)

 expressionToPartialExpression (Solidity.FunctionCallNameValueList expression (Just (Solidity.NameValueList nameValueList))) = (FunctionCallNameValueList (expressionToPartialExpression expression) (Just (Prelude.map (\(Solidity.Identifier id,y) -> (Sym id, (expressionToPartialExpression y))) nameValueList)))

 expressionToPartialExpression (Solidity.FunctionCallExpressionList expression Nothing) = (FunctionCallExpressionList (expressionToPartialExpression expression) Nothing)

 expressionToPartialExpression (Solidity.FunctionCallExpressionList expression (Just (Solidity.ExpressionList expressionList))) = (FunctionCallExpressionList (expressionToPartialExpression expression) (Just (Prelude.map (expressionToPartialExpression) expressionList)))
 
 expressionToPartialExpression (Solidity.TypeCasting typeName expr) = (TypeCasting typeName (expressionToPartialExpression expr))

 expressionToPartialExpression (Solidity.MemberAccess expr (Solidity.Identifier id)) = (MemberAccess (expressionToPartialExpression expr) (Sym id))

 expressionToPartialExpression (Solidity.Literal (Solidity.PrimaryExpressionBooleanLiteral (Solidity.BooleanLiteral "true"))) = Val (BoolType (V True))

 expressionToPartialExpression (Solidity.Literal (Solidity.PrimaryExpressionBooleanLiteral (Solidity.BooleanLiteral "false"))) = Val (BoolType (V False))

 expressionToPartialExpression (Solidity.Literal (Solidity.PrimaryExpressionNumberLiteral (Solidity.NumberLiteralDec noString Nothing))) = Val (IntType (V (read noString :: Integer)))

 expressionToPartialExpression (Solidity.Literal (Solidity.PrimaryExpressionNumberLiteral (Solidity.NumberLiteralHex noString Nothing))) = Val (IntType (V (read noString :: Integer)))
 --TODO hexadecimal numbers, plus units

 expressionToPartialExpression (Solidity.Literal (Solidity.PrimaryExpressionStringLiteral (Solidity.StringLiteral string))) = Val (StringType (V string))

 expressionToPartialExpression (Solidity.Literal (Solidity.PrimaryExpressionTupleExpression (Solidity.RoundBrackets exprs))) = Val (Tuple (Prelude.map expressionToPartialExpression exprs))
 
 expressionToPartialExpression (Solidity.Literal (Solidity.PrimaryExpressionTupleExpression (Solidity.SquareBrackets exprs))) = Val (Tuple (Prelude.map expressionToPartialExpression exprs))

 expressionToPartialExpression (Solidity.Literal (Solidity.PrimaryExpressionIdentifier (Solidity.Identifier id))) = Id (Sym id)

 expressionToPartialExpression (Solidity.New typeName) = Error --to be handled at the level of statement New typeName --New typeName


 ----------------------------------
 --Transitioning
 ----------------------------------

 --step :: ProgramState -> Label -> ProgramState
 --for Label Statement
 --step programState (LabelE (Solidity.Unary string expression)) = 
 --step programState (LabelE (Solidity.Binary "=" (Identifier id) exp)) = push programState id (evaluate exp)
  
 ----------------------------------
 --Evaluation Functions
 ----------------------------------

 evaluate :: ProgramState -> PartialExpression -> PartialExpression
 evaluate programState (Id id) = getValueOf programState id
 evaluate programState (Unary "!" exp) = negation (evaluate programState exp)
 evaluate programState (Unary "++" exp) = incr (evaluate programState exp)
 evaluate programState (Unary "--" exp) = decr (evaluate programState exp)
 evaluate programState (Binary "&&" exp1 exp2) = conjunction (evaluate programState exp1) (evaluate programState exp2)
 evaluate programState ((Binary "||" exp1 exp2)) = disjunction (evaluate programState exp1) (evaluate programState exp2)
 evaluate programState ((Binary "<" exp1 exp2)) = lessThan (evaluate programState exp1) (evaluate programState exp2)
 evaluate programState ((Binary ">" exp1 exp2)) = moreThan (evaluate programState exp1) (evaluate programState exp2)
 evaluate programState ((Binary "<=" exp1 exp2)) = lessThanOrEqual (evaluate programState exp1) (evaluate programState exp2)
 evaluate programState ((Binary ">=" exp1 exp2)) = moreThanOrEqual (evaluate programState exp1) (evaluate programState exp2)
 evaluate programState ((Binary "==" exp1 exp2)) = equal (evaluate programState exp1) (evaluate programState exp2)
 evaluate programState ((Binary "!=" exp1 exp2)) = notEqual (evaluate programState exp1) (evaluate programState exp2)
 evaluate _ _ = Error
--TODO the rest                                            
 
----------------------------------
--Basic Operations Util
----------------------------------
 
 isBoolOp :: String -> Bool
 isBoolOp "!" = True
 isBoolOp "&&" = True
 isBoolOp "||" = True
 isBoolOp "<" = True
 isBoolOp ">" = True
 isBoolOp "<=" = True
 isBoolOp ">=" = True
 isBoolOp "==" = True
 isBoolOp "!=" = True
 isBoolOp _ = False
    
    
 isUnknown :: Value -> Bool
 isUnknown (AddressType Unknown) = True
 isUnknown (BoolType Unknown) = True
 isUnknown (StringType Unknown) = True
 isUnknown (IntType Unknown) = True
 isUnknown (UIntType Unknown) = True
 isUnknown (BytesType Unknown) = True
 isUnknown (ByteType Unknown) = True
 isUnknown (FixedType Unknown) = True
 isUnknown (UfixedType Unknown) = True
 isUnknown _ = False
                 
 ----------------------------------
 --Basic Operations
 ----------------------------------       
 
 negation :: PartialExpression -> PartialExpression
 negation (Val (BoolType (V bool))) = (Val (BoolType (V (not bool))))
 negation (Val (BoolType Unknown)) = (Val (BoolType Unknown))
 negation (Unary "!" exp) = exp
 negation (Binary "&&" exp1 exp2) = (Unary "!" (Binary "&&" exp1 exp2))
 negation (Binary "||" exp1 exp2) = (Unary "!" (Binary "||" exp1 exp2))
 negation (Binary "<" exp1 exp2) = (Binary ">=" exp1 exp2)
 negation (Binary ">" exp1 exp2) = (Binary "<=" exp1 exp2)
 negation (Binary "<=" exp1 exp2) = (Binary ">" exp1 exp2)
 negation (Binary ">=" exp1 exp2) = (Binary "<" exp1 exp2)
 negation (Binary "==" exp1 exp2) = (Binary "!=" exp1 exp2)
 negation (Binary "!=" exp1 exp2) = (Binary "==" exp1 exp2)
 negation (Ternary "?" exp1 exp2 exp3) = case negation exp2 of
                                            Error -> Error
                                            notExp2 -> case negation exp3 of
                                                        Error -> Error
                                                        notExp3 -> (Ternary "?" exp1 notExp2 notExp3)
 negation _ = Error
  
 
 conjunction :: PartialExpression -> PartialExpression -> PartialExpression
 conjunction (Unary "!" _) (Val (BoolType (V False))) = (Val (BoolType (V False)))
 conjunction (Binary op _ _) (Val (BoolType (V False))) = if isBoolOp op
                                                                then (Val (BoolType (V False)))
                                                                else Error
 conjunction (Val (BoolType (V False))) (Unary "!" _) = (Val (BoolType (V False)))
 conjunction (Val (BoolType (V False))) (Binary op _ _) = if isBoolOp op
                                                                then (Val (BoolType (V False)))
                                                                else Error
                                                                
 conjunction (Val (BoolType _)) (Val (BoolType (V False))) = (Val (BoolType (V False)))
 conjunction (Val (BoolType (V False))) (Val (BoolType _)) = (Val (BoolType (V False)))
  
 conjunction (Val (BoolType (V bool1))) (Val (BoolType (V bool2))) = (Val (BoolType (V (bool1 && bool2))))
 conjunction (Val (BoolType Unknown)) (Val (BoolType (V True))) = (Val (BoolType Unknown))
 conjunction (Val (BoolType (V True))) (Val (BoolType Unknown)) = (Val (BoolType Unknown))
  
 conjunction (Ternary "?" exp1 exp2 exp3) (Val (BoolType (V False))) = (Val (BoolType (V False)))
 conjunction (Val (BoolType (V False))) (Ternary "?" exp1 exp2 exp3) = (Val (BoolType (V False)))
 conjunction (Ternary "?" exp1 exp2 exp3) (Val (BoolType bool)) = let newExp2 = conjunction exp2 (Val (BoolType bool))
                                                                      newExp3 = conjunction exp3 (Val (BoolType bool))
                                                                     in (Ternary "?" exp1 newExp2 newExp3)
                                                                       
  
 conjunction (Val (BoolType bool)) (Ternary "?" exp1 exp2 exp3) = let newExp2 = conjunction exp2 (Val (BoolType bool))
                                                                      newExp3 = conjunction exp3 (Val (BoolType bool))
                                                                     in (Ternary "?" exp1 newExp2 newExp3)
 conjunction _ _ = Error
  
 
 disjunction :: PartialExpression -> PartialExpression -> PartialExpression
 disjunction (Unary "!" _) (Val (BoolType (V True))) = (Val (BoolType (V True)))
 disjunction (Binary op _ _) (Val (BoolType (V True))) = if isBoolOp op
                                                                then (Val (BoolType (V True)))
                                                                else Error
 disjunction (Val (BoolType (V True))) (Unary "!" _) = (Val (BoolType (V True)))
 disjunction (Val (BoolType (V True))) (Binary op _ _) = if isBoolOp op
                                                                then (Val (BoolType (V True)))
                                                                else Error
                                                                
 disjunction (Val (BoolType _)) (Val (BoolType (V True))) = (Val (BoolType (V True)))
 disjunction (Val (BoolType (V True))) (Val (BoolType _)) = (Val (BoolType (V True)))
  
 disjunction (Val (BoolType (V bool1))) (Val (BoolType (V bool2))) = (Val (BoolType (V (bool1 || bool2))))
 disjunction (Val (BoolType Unknown)) (Val (BoolType (V False))) = (Val (BoolType Unknown))
 disjunction (Val (BoolType (V False))) (Val (BoolType Unknown)) = (Val (BoolType Unknown))
  
 disjunction (Ternary "?" exp1 exp2 exp3) (Val (BoolType (V True))) = (Val (BoolType (V True)))
 disjunction (Val (BoolType (V True))) (Ternary "?" exp1 exp2 exp3) = (Val (BoolType (V True)))
 disjunction (Ternary "?" exp1 exp2 exp3) (Val (BoolType bool)) = let newExp2 = disjunction exp2 (Val (BoolType bool))
                                                                      newExp3 = disjunction exp3 (Val (BoolType bool))
                                                                     in (Ternary "?" exp1 newExp2 newExp3)
                                                                       
  
 disjunction (Val (BoolType bool)) (Ternary "?" exp1 exp2 exp3) = let newExp2 = disjunction exp2 (Val (BoolType bool))
                                                                      newExp3 = disjunction exp3 (Val (BoolType bool))
                                                                     in (Ternary "?" exp1 newExp2 newExp3)
 disjunction _ _ = Error
 
 
 
 lessThan :: PartialExpression -> PartialExpression -> PartialExpression
 lessThan (Val (IntType (V int1))) (Val (IntType (V int2))) = Val (BoolType (V (int1 < int2)))
 lessThan (Val (IntType (V uint1))) (Ternary "?" exp1 exp2 exp3) = let newExp2 = lessThan exp2 (Val (IntType (V uint1))) 
                                                                       newExp3 = lessThan exp3 (Val (IntType (V uint1))) 
                                                                    in (Ternary "?" exp1 newExp2 newExp3)
 lessThan (Ternary "?" exp1 exp2 exp3) (Val (IntType (V uint1))) = let newExp2 = lessThan exp2 (Val (IntType (V uint1))) 
                                                                       newExp3 = lessThan exp3 (Val (IntType (V uint1))) 
                                                                    in (Ternary "?" exp1 newExp2 newExp3)
                                                                 
 lessThan (Val (UIntType (V uint1))) (Val (UIntType (V uint2))) = Val (BoolType (V (uint1 < uint2)))
 lessThan (Val (UIntType (V uint1))) (Ternary "?" exp1 exp2 exp3) = let newExp2 = lessThan exp2 (Val (UIntType (V uint1))) 
                                                                        newExp3 = lessThan exp3 (Val (UIntType (V uint1))) 
                                                                     in (Ternary "?" exp1 newExp2 newExp3)
 lessThan (Ternary "?" exp1 exp2 exp3) (Val (UIntType (V uint1))) = let newExp2 = lessThan exp2 (Val (UIntType (V uint1))) 
                                                                        newExp3 = lessThan exp3 (Val (UIntType (V uint1))) 
                                                                     in (Ternary "?" exp1 newExp2 newExp3)
 lessThan _ _ = Error
  
 
 
 moreThan :: PartialExpression -> PartialExpression -> PartialExpression
 moreThan (Val (IntType (V int1))) (Val (IntType (V int2))) = Val (BoolType (V (int1 > int2)))
 moreThan (Val (IntType (V uint1))) (Ternary "?" exp1 exp2 exp3) = let newExp2 = moreThan exp2 (Val (IntType (V uint1))) 
                                                                       newExp3 = moreThan exp3 (Val (IntType (V uint1))) 
                                                                     in (Ternary "?" exp1 newExp2 newExp3)
 moreThan (Ternary "?" exp1 exp2 exp3) (Val (IntType (V uint1))) = let newExp2 = moreThan exp2 (Val (IntType (V uint1))) 
                                                                       newExp3 = moreThan exp3 (Val (IntType (V uint1))) 
                                                                     in (Ternary "?" exp1 newExp2 newExp3)
                                                                 
 moreThan (Val (UIntType (V uint1))) (Val (UIntType (V uint2))) = Val (BoolType (V (uint1 > uint2)))
 moreThan (Val (UIntType (V uint1))) (Ternary "?" exp1 exp2 exp3) = let newExp2 = moreThan exp2 (Val (UIntType (V uint1))) 
                                                                        newExp3 = moreThan exp3 (Val (UIntType (V uint1))) 
                                                                      in (Ternary "?" exp1 newExp2 newExp3)
 moreThan (Ternary "?" exp1 exp2 exp3) (Val (UIntType (V uint1))) = let newExp2 = moreThan exp2 (Val (UIntType (V uint1))) 
                                                                        newExp3 = moreThan exp3 (Val (UIntType (V uint1))) 
                                                                      in (Ternary "?" exp1 newExp2 newExp3)
 moreThan _ _ = Error
  
  
 
 lessThanOrEqual :: PartialExpression -> PartialExpression -> PartialExpression
 lessThanOrEqual (Val (IntType (V int1))) (Val (IntType (V int2))) = Val (BoolType (V (int1 <= int2)))
 lessThanOrEqual (Val (IntType (V uint1))) (Ternary "?" exp1 exp2 exp3) = let newExp2 = lessThanOrEqual exp2 (Val (IntType (V uint1))) 
                                                                              newExp3 = lessThanOrEqual exp3 (Val (IntType (V uint1))) 
                                                                            in (Ternary "?" exp1 newExp2 newExp3)
 lessThanOrEqual (Ternary "?" exp1 exp2 exp3) (Val (IntType (V uint1))) = let newExp2 = lessThanOrEqual exp2 (Val (IntType (V uint1))) 
                                                                              newExp3 = lessThanOrEqual exp3 (Val (IntType (V uint1))) 
                                                                            in (Ternary "?" exp1 newExp2 newExp3)
                                                                 
 lessThanOrEqual (Val (UIntType (V uint1))) (Val (UIntType (V uint2))) = Val (BoolType (V (uint1 <= uint2)))
 lessThanOrEqual (Val (UIntType (V uint1))) (Ternary "?" exp1 exp2 exp3) = let newExp2 = lessThanOrEqual exp2 (Val (UIntType (V uint1))) 
                                                                               newExp3 = lessThanOrEqual exp3 (Val (UIntType (V uint1))) 
                                                                             in (Ternary "?" exp1 newExp2 newExp3)
 lessThanOrEqual (Ternary "?" exp1 exp2 exp3) (Val (UIntType (V uint1))) = let newExp2 = lessThanOrEqual exp2 (Val (UIntType (V uint1))) 
                                                                               newExp3 = lessThanOrEqual exp3 (Val (UIntType (V uint1))) 
                                                                             in (Ternary "?" exp1 newExp2 newExp3)
 lessThanOrEqual _ _ = Error
  
  
 
 moreThanOrEqual :: PartialExpression -> PartialExpression -> PartialExpression
 moreThanOrEqual (Val (IntType (V int1))) (Val (IntType (V int2))) = Val (BoolType (V (int1 >= int2)))
 moreThanOrEqual (Val (IntType (V uint1))) (Ternary "?" exp1 exp2 exp3) = let newExp2 = moreThanOrEqual exp2 (Val (IntType (V uint1))) 
                                                                              newExp3 = moreThanOrEqual exp3 (Val (IntType (V uint1))) 
                                                                            in (Ternary "?" exp1 newExp2 newExp3)
 moreThanOrEqual (Ternary "?" exp1 exp2 exp3) (Val (IntType (V uint1))) = let newExp2 = moreThanOrEqual exp2 (Val (IntType (V uint1))) 
                                                                              newExp3 = moreThanOrEqual exp3 (Val (IntType (V uint1))) 
                                                                            in (Ternary "?" exp1 newExp2 newExp3)
                                                                 
 moreThanOrEqual (Val (UIntType (V uint1))) (Val (UIntType (V uint2))) = Val (BoolType (V (uint1 >= uint2)))
 moreThanOrEqual (Val (UIntType (V uint1))) (Ternary "?" exp1 exp2 exp3) = let newExp2 = moreThanOrEqual exp2 (Val (UIntType (V uint1))) 
                                                                               newExp3 = moreThanOrEqual exp3 (Val (UIntType (V uint1))) 
                                                                             in (Ternary "?" exp1 newExp2 newExp3)
 moreThanOrEqual (Ternary "?" exp1 exp2 exp3) (Val (UIntType (V uint1))) = let newExp2 = moreThanOrEqual exp2 (Val (UIntType (V uint1))) 
                                                                               newExp3 = moreThanOrEqual exp3 (Val (UIntType (V uint1))) 
                                                                             in (Ternary "?" exp1 newExp2 newExp3)
 moreThanOrEqual _ _ = Error
  
  
  
 equal :: PartialExpression -> PartialExpression -> PartialExpression
 equal (Val (IntType (V int1))) (Val (IntType (V int2))) = Val (BoolType (V (int1 == int2)))
 equal (Val (IntType (V int))) (Val (IntType Unknown)) = Val (BoolType Unknown)
 equal (Val (IntType Unknown)) (Val (IntType (V int))) = Val (BoolType Unknown)
  
 equal (Val (UIntType (V int1))) (Val (UIntType (V int2))) = Val (BoolType (V (int1 == int2)))
 equal (Val (UIntType (V int))) (Val (UIntType Unknown)) = Val (BoolType Unknown)
 equal (Val (UIntType Unknown)) (Val (UIntType (V int))) = Val (BoolType Unknown)
                                                                   
 equal (Val (BoolType (V bool1))) (Val (BoolType (V bool2))) = (Val (BoolType (V (bool1 == bool2))))
 equal (Val (BoolType Unknown)) (Val (BoolType _)) = (Val (BoolType Unknown))
 equal (Val (BoolType _)) (Val (BoolType Unknown)) = (Val (BoolType Unknown))

 equal (Val (AddressType (V addr1))) (Val (AddressType (V addr2))) = (Val (BoolType (V (addr1 == addr2))))
 equal (Val (AddressType Unknown)) (Val (AddressType _)) = (Val (BoolType Unknown))
 equal (Val (AddressType _)) (Val (AddressType Unknown)) = (Val (BoolType Unknown))
    
 equal exp (Ternary "?" exp1 exp2 exp3) = let newExp2 = equal exp2 exp
                                              newExp3 = equal exp3 exp
                                             in (Ternary "?" exp1 newExp2 newExp3)
 equal (Ternary "?" exp1 exp2 exp3) exp = let newExp2 = equal exp2 exp
                                              newExp3 = equal exp3 exp
                                             in (Ternary "?" exp1 newExp2 newExp3)
 equal _ _ = Error
  
  
  
 notEqual :: PartialExpression -> PartialExpression -> PartialExpression
 notEqual (Val (IntType (V int1))) (Val (IntType (V int2))) = Val (BoolType (V (int1 /= int2)))
 notEqual (Val (IntType (V int))) (Val (IntType Unknown)) = Val (BoolType Unknown)
 notEqual (Val (IntType Unknown)) (Val (IntType (V int))) = Val (BoolType Unknown)
  
 notEqual (Val (UIntType (V int1))) (Val (UIntType (V int2))) = Val (BoolType (V (int1 /= int2)))
 notEqual (Val (UIntType (V int))) (Val (UIntType Unknown)) = Val (BoolType Unknown)
 notEqual (Val (UIntType Unknown)) (Val (UIntType (V int))) = Val (BoolType Unknown)
                                                                   
 notEqual (Val (BoolType (V bool1))) (Val (BoolType (V bool2))) = (Val (BoolType (V (bool1 /= bool2))))
 notEqual (Val (BoolType Unknown)) (Val (BoolType _)) = (Val (BoolType Unknown))
 notEqual (Val (BoolType _)) (Val (BoolType Unknown)) = (Val (BoolType Unknown))

 notEqual (Val (AddressType (V addr1))) (Val (AddressType (V addr2))) = (Val (BoolType (V (addr1 /= addr2))))
 notEqual (Val (AddressType Unknown)) (Val (AddressType _)) = (Val (BoolType Unknown))
 notEqual (Val (AddressType _)) (Val (AddressType Unknown)) = (Val (BoolType Unknown))
    
 notEqual exp (Ternary "?" exp1 exp2 exp3) = let newExp2 = notEqual exp2 exp
                                                 newExp3 = notEqual exp3 exp
                                                in (Ternary "?" exp1 newExp2 newExp3)
 notEqual (Ternary "?" exp1 exp2 exp3) exp = let newExp2 = notEqual exp2 exp
                                                 newExp3 = notEqual exp3 exp
                                                in (Ternary "?" exp1 newExp2 newExp3)
 notEqual _ _ = Error
 

  
 plus :: PartialExpression -> PartialExpression -> PartialExpression
 plus (Val (IntType (V no1))) (Val (IntType (V no2))) = (Val (IntType (V (no1 + no2))))
 plus (Val (UIntType (V no1))) (Val (UIntType (V no2))) = (Val (UIntType (V (no1 + no2))))
 plus _ _ = Error

 incr :: PartialExpression -> PartialExpression
 incr (Val (IntType (V no))) = (Val (IntType (V (no + 1))))
 incr (Val (UIntType (V no))) = (Val (UIntType (V (no + 1))))
 incr _ = Error

 decr :: PartialExpression -> PartialExpression
 decr (Val (IntType (V no))) = (Val (IntType (V (no - 1))))
 decr (Val (UIntType (V no))) = (Val (UIntType (V (no - 1))))
 decr _ = Error

