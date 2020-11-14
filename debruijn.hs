-- This is my attempt at implementing semantics and type checker for the Calculus of Constructions.
-- The rules in the PDF are not algorithmic due to WEAK and CONV. WEAK is easy to handle, but CONV complicates things.
-- I tried to resolve it by computing normal forms of types, since I don't care about efficiency.
-- Ideally I would have a proof that this is correct but I don't. It is working on all the tests I could come up with though.
-- I'm using de Bruijn indices to avoid dealing with substitution, which would be especially annoying since Haskell is purely functional so I can't just have a global counter to generate new free variables.

import Data.Char
import Data.List

-- (Var 0) refers to nearest variable
data AST = Star | Square | Var Integer | App AST AST | Lambda AST AST | Pi AST AST deriving (Eq, Show)

-- Determines if the AST is a value
isValue :: AST -> Bool
isValue Star = True
isValue Square = False
isValue (Var _) = True
isValue (App _ _) = False
isValue (Lambda t e) = isValue t && isValue e
isValue (Pi t e) = isValue t && isValue e


-- increases all de Bruijn indices that pass a given threshold (the free variables)
-- this is used in e.g. substitution.
shiftFree :: Integer -> AST -> AST
shiftFree = shiftFree' 0
  where shiftFree' depth shift Star = Star
        shiftFree' depth shift Square = Square
        shiftFree' depth shift (Var x) = if x<depth then (Var x) else (Var (x+shift))
        shiftFree' depth v (App a1 a2) = (App (shiftFree' depth v a1) (shiftFree' depth v a2))
        shiftFree' depth v (Lambda a1 a2) = (Lambda (shiftFree' depth v a1) (shiftFree' (depth+1) v a2))
        shiftFree' depth v (Pi a1 a2) = (Pi (shiftFree' depth v a1) (shiftFree' (depth+1) v a2))
        
-- subst v a (v is not necessarily a value)
-- (\x:_.a)v => (a[x->v])
subst :: AST -> AST -> AST
subst = subst' 0
  where
        subst' _ _ Star = Star
        subst' _ _ Square = Square
        subst' depth v (Var x) = case (compare x depth) of
                                   LT -> (Var x)
                                   GT -> (Var (x-1))
                                   EQ -> shiftFree depth v
        subst' depth v (App a1 a2) = (App (subst' depth v a1) (subst' depth v a2))
        subst' depth v (Lambda a1 a2) = (Lambda (subst' depth v a1) (subst' (depth+1) v a2))
        subst' depth v (Pi a1 a2) = (Pi (subst' depth v a1) (subst' (depth+1) v a2))

step' :: AST -> AST
step' e = case step e of
  (Just e') -> e'
  Nothing -> error "step should have happened" -- should never happen
  
step :: AST -> Maybe AST
step (Lambda t e) | isValue t && isValue e = Nothing -- Value
                  | isValue t = step e >>= \e' -> Just (Lambda t e') -- LAM2
                  | otherwise = step t >>= \t' -> Just (Lambda t' e) -- LAM1
step (Pi t e) | isValue t && isValue e = Nothing -- Value
                  | isValue t = step e >>= \e' -> Just (Pi t e') -- PI2
                  | otherwise = step t >>= \t' -> Just (Pi t' e) -- PI1
step (App (Lambda t e) v) = Just (subst v e) -- APP3
step (App e1 e2) | isValue e1 && isValue e2 = Nothing
                 | isValue e1 = Just (App e1 (step' e2))-- APP2
                 | otherwise = Just (App (step' e1) e2) -- APP1
step _ = Nothing


-- Repeatedly calls step until it returns Nothing
-- Returns the AST immediately before that
eval :: AST -> AST
eval a = case step a of Nothing -> a ; Just a' -> eval a'

-- Returns normal form of type if successful
-- context is stored in reverse: first element of list is last variable in context 
typeCheck :: [AST] -> AST -> Maybe AST
typeCheck gamma Star = Just Square
typeCheck gamma Square = Nothing
typeCheck gamma (Var x) = case (drop (fromIntegral x) gamma) of
                            (t:_) -> Just (shiftFree (x+1) t)
                            [] -> Nothing
typeCheck gamma (App e1 e2) = typeCheck gamma e1 >>=
                              \t1 -> typeCheck gamma e2 >>=
                              \t2 -> case t1 of
                                (Pi a b) | a==t2 -> Just (eval (subst e2 b))
                                _ -> Nothing
typeCheck gamma (Lambda t e) = typeCheck gamma t >>=
                               \t1 -> typeCheck (t:gamma) e >>=
                               \t2 -> typeCheck (t:gamma) t2 >>=
                               \t3 -> if (t1==Star||t1==Square)&&(t3==Star||t3==Square) then Just (eval (Pi t t2)) else Nothing
typeCheck gamma (Pi t e) = typeCheck gamma t >>=
                           \t1 -> typeCheck (t:gamma) e >>=
                           \t2 -> if (t1==Star||t1==Square)&&(t2==Star||t2==Square) then Just (eval t2) else Nothing


-- Helper function for tests
expectSame :: (Eq a) => (Show a) => a -> a -> IO ()
expectSame expected actual = putStrLn $ if expected == actual then "[PASSED]" else "[FAILED] Expected '" ++ show expected ++ "' found '" ++ show actual ++ "'"

-- Test that f(before) = after
-- Print an error message if not
test :: (Eq b) => (Show a) => (Show b) => (a -> b) -> a -> b -> IO ()
test f before after = putStr ("  Testing " ++ (show before) ++ ": ") >> expectSame after (f before)

-- Test that repeatedly stepping the first expression generates the rest
testStepSeq :: [AST] -> IO ()
testStepSeq (x:(y:ys)) = test step x (Just y) >> testStepSeq (y:ys)
testStepSeq (x:[]) = test step x Nothing
testStepSeq _ = return ()


-- Simple parser for readable test cases
-- (Parsing and error handling is not the focus of this project)
--  * for Star
-- [0-9] for free variables
-- [a-zA-Z] for bound variables
-- (&x:A.B) for Lambda
-- (#x:A.B) for PI
-- (A B) for APP
parse :: String -> AST
parse input = case parse' [] input of
                (output,[]) -> output
                _ -> error "Expected EOL"
  where
    parse' :: [Char] -> [Char] -> (AST,[Char])
    parse' env ('*':input') = (Star,input')
    parse' env (d:input') | isDigit d = ((Var (toInteger ((length env)+(digitToInt d)))),input')
    parse' env (c:input') | isAlpha c = case findIndex (==c) env of
                                                    (Just x) -> (Var (toInteger x),input')
                                                    Nothing -> error "syntax error"
    parse' env ('(':'&':x:':':input') | isAlpha x = let (a,input) = parse' env input' in
                                                       case input of
                                                         ('.':input') -> let (b,input) = parse' (x:env) input' in
                                                           case input of
                                                             ')':input' -> ((Lambda a b),input')
                                                             _ -> error "syntax error"
                                                         _ -> error "syntax error"
    parse' env ('(':'#':x:':':input') | isAlpha x = let (a,input) = parse' env input' in
                                                       case input of
                                                         ('.':input') -> let (b,input) = parse' (x:env) input' in
                                                           case input of
                                                             ')':input' -> ((Pi a b),input')
                                                             _ -> error "syntax error"
                                                         _ -> error "syntax error"
    parse' env ('(':input) = let (a,input') = parse' env input in
                                let (b,input'') = parse' env input' in
                                  case input'' of
                                    ')':input''' -> ((App a b),input''')
                                    _ -> error "syntax error"

main :: IO ()
main =
  putStrLn "Testing isValue"
  >> test isValue Star True
  >> test isValue Square False
  
  >> test isValue (Var 0) True
  
  >> test isValue (App Star Star) False
  >> test isValue (App Star Square) False
  >> test isValue (App Square Star) False
  >> test isValue (App Square Square) False
  
  >> test isValue (Lambda Star Star) True
  >> test isValue (Lambda Star Square) False
  >> test isValue (Lambda Square Star) False
  >> test isValue (Lambda Square Square) False
  
  >> test isValue (Pi Star Star) True
  >> test isValue (Pi Star Square) False
  >> test isValue (Pi Square Star) False
  >> test isValue (Pi Square Square) False

  >> putStrLn "Testing substitution (using de Brujin indices)"
  >> test (subst (Lambda Star (Var 0))) (Lambda Square (Var 0)) (Lambda Square (Var 0))
  >> test (subst (Lambda Star (Var 0))) (Lambda Square (Var 2)) (Lambda Square (Var 1))
  >> test (subst (Lambda Star (Var 0))) (Lambda Square (Var 3)) (Lambda Square (Var 2))
  >> test (subst (Lambda Star (Var 0))) (Lambda Square (Var 1)) (Lambda Square (Lambda Star (Var 0)))
  >> test (subst (Lambda Star (Var 1))) (Lambda Square (Var 1)) (Lambda Square (Lambda Star (Var 2)))
  
  >> test (subst (Pi Star (Var 0))) (Pi Square (Var 0)) (Pi Square (Var 0))
  >> test (subst (Pi Star (Var 0))) (Pi Square (Var 2)) (Pi Square (Var 1))
  >> test (subst (Pi Star (Var 0))) (Pi Square (Var 3)) (Pi Square (Var 2))
  >> test (subst (Pi Star (Var 0))) (Pi Square (Var 1)) (Pi Square (Pi Star (Var 0)))
  >> test (subst (Pi Star (Var 1))) (Pi Square (Var 1)) (Pi Square (Pi Star (Var 2)))

  >> test (subst (Lambda Star (Var 1))) (Lambda (Var 0) (Var 1)) (Lambda (Lambda Star (Var 1)) (Lambda Star (Var 2)))
  >> test (subst (Lambda (Var 0) (Var 1))) (Lambda (Var 0) Square) (Lambda (Lambda (Var 0) (Var 1)) Square)
  >> test (subst (Lambda (Var 0) (Var 1))) (Lambda (Var 1) Square) (Lambda (Var 0) Square)
  >> test (subst (Lambda (Var 0) (Var 1))) (Lambda (Var 2) Square) (Lambda (Var 1) Square)
  >> test (subst (Var 10)) (App (Var 0) (Var 0)) (App (Var 10) (Var 10))
  >> test (subst (Var 10)) (App (Var 1) (Var 1)) (App (Var 0) (Var 0))
  
  >> putStrLn "Testing lambda calculus (ignoring types)"
  >> (let i = (Lambda Star (Var 0))
          ii = (App i i)
          sii = (Lambda Star (App (Var 0) (Var 0)))
          omega = (App sii sii) in
        test step i Nothing
        >> test step sii Nothing
        >> test step omega (Just omega)
        >> test step (App i sii) (Just sii) -- rule APP3's substitution
        >> testStepSeq [(App (App sii i) i),(App ii i),ii,i]
        >> testStepSeq [(Lambda ii ii),(Lambda i ii),(Lambda i i)] -- rules LAM1 and LAM2
        >> testStepSeq [(Pi ii ii),(Pi i ii),(Pi i i)] -- rules PI1 and PI2
        >> test step (App (Lambda ii ii) ii) (Just ii) -- rule APP3
        >> test step (App (Lambda i i) ii) (Just i)
        >> testStepSeq [(App ii ii),(App i ii),(App i i),i] -- rule APP1 and APP2
     )
  >> putStrLn "Testing parser"
  >> test parse "*" Star
  >> test parse "(&x:*.*)" (Lambda Star Star)
  >> test parse "(&x:*.x)" (Lambda Star (Var 0))
  >> test parse "0" (Var 0)
  >> test parse "2" (Var 2)
  >> test parse "(&x:0.0)" (Lambda (Var 0) (Var 1))
  >> test parse "(**)" (App Star Star)
  >> test parse "((&x:*.x)(&y:*.y))" (App (Lambda Star (Var 0)) (Lambda Star (Var 0)))
  >> test parse "((#x:*.x)(#y:*.0))" (App (Pi Star (Var 0)) (Pi Star (Var 1)))
  
  --Remember that the context is stored backwards
  --Notice that in (Lambda (Var 0) (Var 0)), the two (Var 0) refer to different variables because a new variable is in scope of the second one.
  --To refer to the same variable, (Lambda (Var 0) (Var 1)) is needed
  >> putStrLn "Testing type checking"
  >> test (typeCheck []) Square Nothing
  >> test (typeCheck []) Star (Just Square)
  >> test (typeCheck [Star]) Star (Just Square)
  >> test (typeCheck []) (Var 0) Nothing
  >> test (typeCheck [Star]) (Var 0) (Just Star)
  >> test (typeCheck [Star]) (Var 1) Nothing
  >> test (typeCheck [(Var 0),Star,Star]) (Var 0) (Just (Var 1))
  >> test (typeCheck [(Var 1),Star,Star]) (Var 0) (Just (Var 2))
  >> test (typeCheck [Star,(Var 0),Star]) (Var 1) (Just (Var 2)) -- testing index shift
  >> test (typeCheck []) (Pi Star Star) (Just Square)
  >> test (typeCheck []) (Pi Star (Var 0)) (Just Star) -- I don't this type is inhabited: (#x:*.x):*
  >> test (typeCheck []) (Lambda Star Star) Nothing -- Can't return kinds, only types
  >> test (typeCheck []) (Lambda Star (Var 0)) (Just (Pi Star Star))
  >> test (typeCheck [(Pi Star Star)]) (Lambda Star (Var 1)) (Just (Pi Star (Pi Star Star)))
  >> test (typeCheck [Star]) (App (Lambda Star (Var 0)) (Var 0)) (Just Star) -- testing identity function on types (in the context where S:*), (&T:*.T)S:*
  >> test (typeCheck [Star]) (App (Lambda (Pi Star Star) (Var 0)) (Var 0)) Nothing --mismatched input type (&T:*->*.T)S but S:*
  >> test (typeCheck [Star]) (Lambda (Var 0) (Var 1)) (Just (Pi (Var 0) Star)) -- (in the context where T:*), (&x:T.T):(#x:T.*)
  >> test (typeCheck [Star]) (Lambda (Var 0) (Var 0)) (Just (Pi (Var 0) (Var 1))) -- identity function on fixed type: (&x:T.x):(#x:T.T)
  >> test (typeCheck []) (Lambda Star (Lambda (Var 0) (Var 0))) (Just (Pi Star (Pi (Var 0) (Var 1)))) -- polymorphic identity function (&T:*.(&x:T.x))
  -- tests are becoming unreadable. Using parser now.
  -- (repeats some earlier tests)
  >> test (typeCheck [Star]) (parse "(&T:*.T)") (Just (parse "(#T:*.*)")) -- identity function on types
  >> test (typeCheck [Star]) (parse "((&T:*.T)0)") (Just (parse "*")) -- using identity function on types
  >> test (typeCheck [Star]) (parse "((&T:(#x:*.*).T)0)") Nothing -- mismatched input type
  >> test (typeCheck [Star]) (parse "(&x:0.x)") (Just (parse "(#x:0.0)")) -- identity function on fixed type
  >> test (typeCheck []) (parse "(&T:*.(&x:T.x))") (Just (parse "(#T:*.(#x:T.T))")) -- polymorphic identity function
  >> test (typeCheck []) (parse "(&T:*.(&f:(#x:T.T).(&x:T.x)))") (Just (parse "(#T:*.(#f:(#x:T.T).(#x:T.T)))")) -- encoding for number 0
  >> test (typeCheck []) (parse "(&T:*.(&f:(#x:T.T).(&x:T.(fx))))") (Just (parse "(#T:*.(#f:(#x:T.T).(#x:T.T)))")) -- number 1
  >> test (typeCheck []) (parse "(&T:*.(&f:(#x:T.T).(&x:T.(f(fx)))))") (Just (parse "(#T:*.(#f:(#x:T.T).(#x:T.T)))")) -- number 2
  >> test (typeCheck [Star]) (parse "((&T:*.(&f:(#x:T.T).(&x:T.(f(fx)))))0)") (Just (parse "(#f:(#x:0.0).(#x:0.0))")) -- number 2 with first argument applied
  >> test (typeCheck []) (parse "(#T:*.T)") (Just (parse "*")) -- bottom: can be typed but not inhabited
  >> test (typeCheck []) (parse "(&T:*.(#x:T.T))") (Just (parse "(#T:*.*)")) -- arrow type constructor
  >> test (typeCheck []) (parse "(&A:*.(&B:*.(#C:*.(#f:(#x:A.C).(#g:(#x:B.C).C)))))") (Just (parse "(#A:*.(#B:*.*))")) -- or type constructor
  >> test (typeCheck []) (parse "(&A:*.(&B:*.(&a:A.(&C:*.(&f:(#x:A.C).(&g:(#x:B.C).(fa)))))))") (Just (parse "(#A:*.(#B:*.(#a:A.(#C:*.(#f:(#x:A.C).(#g:(#x:B.C).C))))))")) -- inject left
  >> test (typeCheck []) (parse "(&A:*.(&B:*.(&b:B.(&C:*.(&f:(#x:A.C).(&g:(#x:B.C).(gb)))))))") (Just (parse "(#A:*.(#B:*.(#b:B.(#C:*.(#f:(#x:A.C).(#g:(#x:B.C).C))))))")) -- inject right
  >> test (typeCheck []) (parse "(&A:*.(&B:*.(&a:A.(&C:*.(&f:(#x:A.C).(&g:(#x:B.C).(ga)))))))") Nothing -- type mismatch
  >> test (typeCheck [Star]) (parse "(&x:0.0)") (Just (parse "(#x:0.*)")) -- types "depending" on terms
  -- I had trouble finding less trivial inhabited dependent product types...
        
         
          
