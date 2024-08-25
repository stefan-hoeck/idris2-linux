module CP

import Data.Maybe0
import Data.Array.Index
import System.Linux.File
import System

%default total

bufferSize : Bits32
bufferSize = 0x10000

tryLT : (m,n : Nat) -> Maybe0 (LT m n)
tryLT m n with (m < n) proof eq
  _ | True  = Just0 (ltOpReflectsLT m n eq)
  _ | False = Nothing0

covering
drain : FileDesc b => {n : _} -> b -> ByteVect n -> IO (Either FileError ())
drain fd bv =
  writeVect fd bv >>= \case
    WAgain    => drain fd bv
    WErr x    => pure (Left $ WriteErr x)
    Written m => case tryLT m n of
      Nothing0 => pure (Right ())
      Just0 _  => drain fd (drop m bv)

covering
cp : FileDesc a => FileDesc b => a -> b -> IO (Either FileError ())
cp i o = do
  read i bufferSize >>= \case
    EOF       => pure $ Right ()
    Again     => cp i o
    Err x     => pure $ Left (ReadErr x)
    Bytes m b =>
      drain o (BV b 0 reflexive) >>= \case
        Right () => cp i o
        Left err => pure (Left err)

export covering
copy : IO ()
copy = do
  [_,is,os] <- getArgs | _ => putStrLn "invalid number of args"
  pure ()
