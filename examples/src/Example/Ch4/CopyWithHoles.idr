module Example.Ch4.CopyWithHoles

import Example.Util.File
import Example.Util.Opts

%default total

usage : String
usage =
  """
  Usage: linux-examples copyh SOURCE DEST

  This works like `copy` but keeps file holes while `copy` will fill holes
  with explicit zeroes.

  Set `$LI_BUF_SIZE` to change the used buffer size (default: 65536).
  """

parameters {auto hf : Has Errno es}

  covering
  writeBlocks : FileDesc a => a -> (n : Nat) -> ByteVect n -> Prog es ()
  writeBlocks o 0 bv = pure ()
  writeBlocks o k bv =
    let MkBreakRes l1 l2 bv1 bv2 _ := break (0 ==) bv
        MkBreakRes l3 l4 bv3 bv4 _ := break (0 /=) bv2
     in do
          fwrite o (BS l1 bv1)
          ignore $ lseek o (cast l3) SEEK_CUR
          writeBlocks o l4 bv4

  covering
  copy : FileDesc a => FileDesc b => Bits32 -> a -> b -> Prog es ()
  copy buf i o = ignore $ stream _ i buf (\(BS n bv) => writeBlocks o n bv)

  covering
  cp : Bits32 -> String -> String -> Prog es ()
  cp buf i o =
    use [openFile i 0 0, openFile o create 0o660] $ \[fi,fo] => copy buf fi fo

  export covering
  copyh : Has ArgErr es => List String -> Prog es ()
  copyh ["--help"] = stdoutLn usage
  copyh [i,o] = do
    fi  <- readOptIO OPath i
    fo  <- readOptIO OPath o
    buf <- parseEnv OBits32 "LI_BUF_SIZE" 0x10000
    cp buf fi fo
  copyh _ = throw (WrongArgs usage)
