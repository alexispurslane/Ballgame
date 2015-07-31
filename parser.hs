-- | The main module parsers and executes the R6RS Scheme superset, Ballgame
module Main where

import Text.ParserCombinators.Parsec hiding (spaces)

import System.Environment
import System.IO

import Control.Monad
import Control.Monad.Except

import Data.Char
import Data.Maybe
import Data.IORef
import Data.Either

-- | The Scheme environment
type Env = IORef [(String, IORef LispVal)]


nullEnv :: IO Env
nullEnv = newIORef []

type IOThrowsError = ExceptT LispError IO

liftThrows :: ThrowsError a -> IOThrowsError a
liftThrows (Left err) = throwError err
liftThrows (Right val) = return val

runIOThrows :: IOThrowsError String -> IO String
runIOThrows action = liftM extractValue $ runExceptT $ trapError action

isBound :: Env -> String -> IO Bool
isBound envRef var = liftM (isJust . lookup var) (readIORef envRef)

getVar :: Env -> String -> IOThrowsError LispVal
getVar envRef var = do
  env <- liftIO $ readIORef envRef
  maybe (return $ Atom var)
        (liftIO . readIORef)
        (lookup var env)

setVar :: Env -> String -> LispVal -> IOThrowsError LispVal
setVar envRef var value = do
  env <- liftIO $ readIORef envRef
  maybe (throwError $ UnboundVar "Setting an unbound variable" var)
        (liftIO . flip writeIORef value)
        (lookup var env)
  return value

defineVar :: Env -> String -> LispVal -> IOThrowsError LispVal
defineVar envRef var value = do
  alreadyDefined <- liftIO $ isBound envRef var
  if alreadyDefined
    then setVar envRef var value >> return value
    else liftIO $ do
      valueRef <- newIORef value
      env <- readIORef envRef
      writeIORef envRef ((var, valueRef) : env)
      return value

bindVars :: Env -> [(String, LispVal)] -> IO Env
bindVars envRef bindings = readIORef envRef >>= extendEnv bindings >>= newIORef
  where extendEnv bindings env = liftM (++ env) (mapM addBindings bindings)
        addBindings (var, values) = do
          ref <- newIORef values
          return (var, ref)

-- | Possible Scheme values
data LispVal = Atom String
             | List [LispVal]
             | Number Integer
             | Decimal Double
             | String String
             | Bool Bool
             | Char Char
             | PrimitiveFunc ([LispVal] -> ThrowsError LispVal)
             | Func { params :: [String],
                      vararg :: Maybe String,
                      body :: [LispVal],
                      closure :: Env
                    }
              | IOFunc ([LispVal] -> IOThrowsError LispVal)
              | Port Handle
instance Show LispVal where show = showVal

-- | Possible Scheme Errors
data LispError = NumArgs Integer [LispVal]
               | TypeMismatch String LispVal
               | Parser ParseError
               | BadSpecialForm String LispVal
               | NotFunction String String
               | UnboundVar String String
               | Default String
instance Show LispError where show = showError

type ThrowsError = Either LispError

-- | Represents a value unpacker
data Unpacker = forall a. Eq a => AnyUnpacker (LispVal -> ThrowsError a)

-- | Recognizes a Scheme symbol
symbol :: Parser Char
symbol = oneOf "!#$%&|*+-/:<=>?@^_~"

-- | Skips spaces
spaces :: Parser ()
spaces = skipMany1 (oneOf " ")

-- | Returns a LispVal String read from a String
parseString :: Parser LispVal
parseString = do
  char '"'
  x <- many (escapedChar <|> noneOf "\\\"")
  char '"'
  return $ String x

parseChar :: Parser LispVal
parseChar = do
  string "#\\"
  s <- many1 letter
  return $ case map toLower s of
    "space" -> Char ' '
    "newline" -> Char '\n'
    "return" -> Char '\r'
    "linefeed" -> Char '\f'
    "tab" -> Char '\t'
    "vtab" -> Char '\v'
    "backspace" -> Char '\b'
    [x] -> Char x

-- | A helper function for parseString. Matches an escaped character
escapedChar :: Parser Char
escapedChar = do
  char '\\'
  c <- oneOf "\\abtnvfr\""
  return $ case c of
    '\\' -> c
    'a' -> '\a'
    'b' -> '\b'
    't' -> '\t'
    'n' -> '\n'
    'v' -> '\v'
    'f' -> '\f'
    'r' -> '\r'
    '"' -> c

-- | Match a list of expressions spearated by spaces
parseList :: Parser LispVal
parseList = liftM List $ sepBy parseExpr spaces

-- | Parse a quoted symbol/expression
parseQuoted :: Parser LispVal
parseQuoted = do
  char '\''
  x <- parseExpr
  return $ List [Atom "quote", x]

parseQuasiquoted :: Parser LispVal
parseQuasiquoted = do
  char '`'
  x <- parseExpr
  return $ List [Atom "quasiquote", x]

parseUnquoted :: Parser LispVal
parseUnquoted = do
  char ','
  x <- parseExpr
  return $ List [Atom "unquote", x]

-- | Returns a LispVal Atom read from a String
parseAtom :: Parser LispVal
parseAtom = do
  first <- letter <|> symbol
  rest <- many (letter <|> digit <|> symbol)
  let atom = first:rest


  return $ case atom of
    "#t" -> Bool True
    "#f" -> Bool False
    _    -> Atom atom

-- | Returns a LispVal Number read from a String
parseNumber :: Parser LispVal
parseNumber = liftM readWrap $ many1 digit
  where readWrap = Number . read

-- | Returns a LispVal Decimal read from a String
parseDecimal :: Parser LispVal
parseDecimal = do
  whole <- many1 digit
  char '.'
  decimal <- many1 digit
  return $ Decimal (read (whole++"."++decimal))

-- | Parses a Scheme expression
parseExpr :: Parser LispVal
parseExpr = parseAtom
  <|> parseString
  <|> try parseDecimal
  <|> try parseNumber
  <|> parseQuoted
  <|> parseQuasiquoted
  <|> parseUnquoted
  <|> do oneOf "({["
         x <- try parseList
         oneOf ")}]"
         return x

-- | Formats Scheme values
showVal :: LispVal -> String
showVal (String contents) = "\"" ++ contents ++ "\""
showVal (Atom name) = name
showVal (Number contents) = show contents
showVal (Decimal contents) = show contents
showVal (Bool True) = "#t"
showVal (Bool False) = "#f"
showVal (List contents) = "(" ++ unwordsList contents ++ ")"
showVal (PrimitiveFunc name) = "<primitive>"
showVal (Func {params = args, vararg = varargs, body = body, closure = env}) =
  "(lambda (" ++ unwords args ++
    (case varargs of
      Nothing -> ""
      Just arg -> " . " ++ arg) ++ ") " ++ unwords (map showVal body) ++ ")"
showVal (Port _) = "<port>"
showVal (IOFunc _)= "<I/O function>"

-- | Formats Scheme Error
showError :: LispError -> String
showError (UnboundVar message varname) = message ++ ": " ++ varname
showError (BadSpecialForm message form) = message ++ ": " ++ show form
showError (NotFunction message func) = message ++ ": " ++ show func
showError (NumArgs expected found) = "Expected " ++ show expected ++ " args: found values " ++ unwordsList found
showError (TypeMismatch expected found) = "Invalid type: expected " ++ expected ++ ", found " ++ show found
showError (Parser parseErr) = "Parse error at " ++ show parseErr

-- | Convert error to string, and return it
trapError action = catchError action (return . show)

-- | Possibly throws an error when extracting a Scheme values
extractValue :: ThrowsError a -> a
extractValue (Right val) = val

-- | Recursivly formats a list
unwordsList :: [LispVal] -> String
unwordsList = unwords . map showVal

-- | EVALUATION AND INPUT | --

-- | A set of built in functions and primitive operators
primitives :: [(String, [LispVal] -> ThrowsError LispVal)]
primitives = [("+", numericBinop (+)),
              ("*", numericBinop (*)),
              ("-", numericBinop (-)),
              ("/", numericBinop div),
              ("mod", numericBinop mod),
              ("quotient", numericBinop quot),
              ("remainder", numericBinop rem),
              ("=", numBoolBinop (==)),
              ("<", numBoolBinop (<)),
              (">", numBoolBinop (>)),
              ("!=", numBoolBinop (/=)),
              (">=", numBoolBinop (>=)),
              ("<=", numBoolBinop (<=)),
              ("and", boolBoolBinop (&&)),
              ("or", boolBoolBinop (||)),
              ("string=?", strBoolBinop (==)),
              ("string>?", strBoolBinop (>)),
              ("string<?", strBoolBinop (<)),
              ("string<=?", strBoolBinop (<=)),
              ("string>=?", strBoolBinop (>=)),
              ("string-append", stringAppend),
              ("car", car),
              ("first", car),
              ("cdr", cdr),
              ("rest", cdr),
              ("cons", cons),
              ("prepend", cons),
              ("eq?", eqv),
              ("eqv?", eqv),
              ("equal?", equal)]

primitiveBindings :: IO Env
primitiveBindings = nullEnv >>= flip bindVars (map (makeFunc IOFunc) ioPrimitives
                                                ++ map (makeFunc PrimitiveFunc) primitives)
  where makeFunc constructor (var, func) = (var, constructor func)

-- | Adaptes a Haskell functions for Scheme
numericBinop :: (Integer -> Integer -> Integer) -> [LispVal] -> ThrowsError LispVal
numericBinop op singleVal@[_] = throwError $ NumArgs 2 singleVal
numericBinop op params = liftM (Number . foldl1 op) (mapM unpackNum params)

unpackNum :: LispVal -> ThrowsError Integer
unpackNum (Number n) = return n
unpackNum (String n) = let parsed = reads n in
  if null parsed
    then throwError $ TypeMismatch "number" $ String n
    else return $ fst $ head parsed
unpackNum (List [n]) = unpackNum n
unpackNum notNum = throwError $ TypeMismatch "number" notNum

boolBinop :: (LispVal -> ThrowsError a) -> (a -> a -> Bool) -> [LispVal] -> ThrowsError LispVal
boolBinop unpacker op args = if length args /= 2
                             then throwError $ NumArgs 2 args
                             else do left <- unpacker $ head args
                                     right <- unpacker $ args !! 1
                                     return $ Bool $ left `op` right

numBoolBinop = boolBinop unpackNum
strBoolBinop = boolBinop unpackStr
boolBoolBinop = boolBinop unpackBool

unpackStr :: LispVal -> ThrowsError String
unpackStr (String s) = return s
unpackStr (Number s) = return $ show s
unpackStr (Bool s) = return $ show s
unpackStr notString = throwError $ TypeMismatch "string" notString

unpackBool :: LispVal -> ThrowsError Bool
unpackBool (Bool b) = return b
unpackBool notBool = throwError $ TypeMismatch "boolean" notBool

-- | Takes an Unpacker and two LispVals, and determines if the LispVals are equel when unpacked with the Unpacker
unpackEquals :: LispVal -> LispVal -> Unpacker -> ThrowsError Bool
unpackEquals arg1 arg2 (AnyUnpacker unpacker) =
  do
    unpacked1 <- unpacker arg1
    unpacked2 <- unpacker arg2
    return $ unpacked1 == unpacked2
  `catchError` const (return False)

-- | Checks if two LispVals are equal in any possible way
equal :: [LispVal] -> ThrowsError LispVal
equal [List arg1, List arg2] = return $ Bool $ length arg1 == length arg2 && all equalPair (zip arg1 arg2)
  where equalPair (x1, x2) = case equal [x1, x2] of
                               Left err -> False
                               Right (Bool val) -> val
equal [arg1, arg2] = do
  primitiveEquals <- liftM or $ mapM (unpackEquals arg1 arg2)
                     [AnyUnpacker unpackNum, AnyUnpacker unpackStr, AnyUnpacker unpackBool]
  eqvEquals <- eqv [arg1, arg2]
  return $ Bool $ primitiveEquals || let (Bool x) = eqvEquals in x
equal badArgList = throwError $ NumArgs 2 badArgList
-- | Primitive list access functions
car :: [LispVal] -> ThrowsError LispVal
car [List (x : xs)] = return x
car [String (x : xs)] = return $ String [x]
car [badArg] = throwError $ TypeMismatch "pair" badArg
car badArgList = throwError $ NumArgs 1 badArgList

cdr :: [LispVal] -> ThrowsError LispVal
cdr [List (x : xs)] = return $ List xs
cdr [String (x : xs)] = return $ String xs
cdr [badArg] = throwError $ TypeMismatch "pair" badArg
cdr badArgList = throwError $ NumArgs 1 badArgList

-- | Primitive list building function, CONS
cons :: [LispVal] -> ThrowsError LispVal
cons [x1, List []] = return $ List [x1]
cons [x, List xs] = return $ List $ x : xs
cons [x1, x2] = return $ List $ x1 : [x2]
cons badArgList = throwError $ NumArgs 2 badArgList

-- | Checks if two LispVals are exactly equivilant and equal
eqv :: [LispVal] -> ThrowsError LispVal
eqv [Bool arg1, Bool arg2] = return $ Bool $ arg1 == arg2
eqv [Number arg1, Number arg2] = return $ Bool $ arg1 == arg2
eqv [String arg1, String arg2] = return $ Bool $ arg1 == arg2
eqv [Atom arg1, Atom arg2] = return $ Bool $ arg1 == arg2
eqv [List arg1, List arg2] = return $ Bool $ length arg1 == length arg2 && all eqvPair (zip arg1 arg2)
  where eqvPair (x1, x2) = case eqv [x1, x2] of
                             Left err -> False
                             Right (Bool val) -> val
eqv [_, _] = return $ Bool False
eqv badArgList = throwError $ NumArgs 2 badArgList

-- | Append two strings
stringAppend :: [LispVal] -> ThrowsError LispVal
stringAppend [String x1, String x2] = return $ String $ x1 ++ x2
stringAppend [x1, x2] =  return $ String $ showVal x1 ++ showVal x2

-- | IO Primitive functions

ioPrimitives :: [(String, [LispVal] -> IOThrowsError LispVal)]
ioPrimitives = [("apply", applyProc),
                ("open-input-file", makePort ReadMode),
                ("open-output-file", makePort WriteMode),
                ("close-port", closePort),
                ("read", readProc),
                ("write", writeProc),
                ("read-contents", readContents),
                ("read-all", readAll)]

applyProc :: [LispVal] -> IOThrowsError LispVal
applyProc [func, List args] = apply func args
applyProc (func : args) = apply func args

makePort :: IOMode -> [LispVal] -> IOThrowsError LispVal
makePort mode [String filename] = liftM Port $ liftIO $ openFile filename mode

closePort :: [LispVal] -> IOThrowsError LispVal
closePort [Port port] = liftIO $ hClose port >> return (Bool True)
closePort _ = return $ Bool False

readProc :: [LispVal] -> IOThrowsError LispVal
readProc [] = readProc [Port stdin]
readProc [Port port] = liftIO (hGetLine port) >>= liftThrows . readExpr

writeProc :: [LispVal] -> IOThrowsError LispVal
writeProc [obj] = writeProc [obj, Port stdout]
writeProc [obj, Port port] = liftIO $ hPrint port obj >> return (Bool True)

readContents :: [LispVal] -> IOThrowsError LispVal
readContents [String filename] = liftM String $ liftIO $ readFile filename

load :: String -> IOThrowsError [LispVal]
load filename = liftIO (readFile filename) >>= liftThrows . readExprList

readAll :: [LispVal] -> IOThrowsError LispVal
readAll [String filename] = liftM List $ load filename

-- | Evaluates primitives
eval :: Env -> LispVal -> IOThrowsError LispVal
eval env val@(String _) = return val
eval env val@(Number _) = return val
eval env val@(Decimal _) = return val
eval env val@(Bool _) = return val
eval env (Atom id) = getVar env id >>= eval env
eval env (List [Atom "quote", val]) = return val
eval env (List [Atom "quasiquote", val]) = qeval env val
eval env (List [Atom "if", pred, conseq, alt]) = do
    result <- eval env pred
    case result of
      Bool False -> eval env alt
      otherwise -> eval env conseq
eval env (List [Atom "define", Atom var, form]) = defineVar env var form
eval env (List (Atom "lambda" : List params : body)) = makeNormalFunc env params body
eval env (PrimitiveFunc f) = return $ PrimitiveFunc f
eval env (IOFunc f) = return $ IOFunc f
eval env (List [Atom "load", String filename]) = load filename >>= liftM last . mapM (eval env)
eval env (List (function : args)) = do
  func <- eval env function
  case func of
    PrimitiveFunc _ -> mapM (eval env) args >>= apply func
    Func {} -> apply func args
    IOFunc _ -> mapM (eval env) args >>= apply func
eval env badForm = throwError $ BadSpecialForm "Unrecognized special form" badForm

qeval :: Env -> LispVal -> IOThrowsError LispVal
qeval env (List [Atom "unquote", val]) = eval env val
qeval env (List val) = liftM List (mapM (qeval env) val)
qeval env (val) = return val

makeFunc varargs env params body = return $ Func (map showVal params) varargs body env
makeNormalFunc = makeFunc Nothing

-- | Runs a function on LispVal arguments
apply :: LispVal -> [LispVal] -> IOThrowsError LispVal
apply (PrimitiveFunc func) args = liftThrows $ func args
apply (Func params varargs body closure) args =
  if num params /= num args && isNothing varargs
    then throwError $ NumArgs (num params) args
    else liftIO (bindVars closure $ zip params args) >>= evalBody
  where
    num = toInteger . length
    evalBody env = liftM last $ mapM (eval env) body
apply (IOFunc func) args = func args

-- | Reads a Scheme expression
readOrThrow :: Parser a -> String -> ThrowsError a
readOrThrow parser input = case parse parser "Ballgame Scheme" input of
  Left err -> throwError $ Parser err
  Right val -> return val

readExpr = readOrThrow parseExpr
readExprList = readOrThrow (endBy parseExpr spaces)

-- | Main entry point and IO related code
flushStr :: String -> IO ()
flushStr str = putStr str >> hFlush stdout

readPrompt :: String -> IO String
readPrompt prompt = flushStr prompt >> getLine

evalString :: Env -> String -> IO String
evalString env expr = runIOThrows $ liftM show $ liftThrows (readExpr expr) >>= eval env

evalAndPrint :: Env -> String -> IO ()
evalAndPrint env expr = evalString env expr >>= putStrLn

until_ :: Monad m => (a -> Bool) -> m a -> (a -> m ()) -> m ()
until_ pred prompt action = do
  result <- prompt
  unless (pred result) $ action result >> until_ pred prompt action

runOne :: [String] -> IO ()
runOne args = do
  env <- primitiveBindings >>= flip bindVars [("args", List $ map String $ drop 1 args)]
  runIOThrows (liftM show $ eval env (List [Atom "load", String (head args)])) >>= hPutStrLn stderr

runRepl :: IO ()
runRepl = primitiveBindings >>= until_ (== "quit") (readPrompt "BG :) ") . evalAndPrint

main :: IO ()
main = do
  args <- getArgs
  if null args then runRepl else runOne args
