module System.Posix.File.ReadRes

import Derive.Prelude
import Data.Linear.Token

import Data.Vect
import public Data.Buffer
import public Data.Buffer.Core
import public Data.ByteString
import public Data.C.Ptr
import public System.Posix.Errno

%default total
%language ElabReflection

||| Result of a (potentially non-blocking) read, typically from a pipe
||| or socket.
public export
data ReadRes : Type -> Type where
  ||| The system call was interrupted by a signal.
  Interrupted : ReadRes a

  ||| There is currently no data avialable (this will only be a possible
  ||| outcome when reading in non-blocking mode).
  NoData      : ReadRes a

  ||| Tried to read from a closed connection or pipe.
  Closed      : ReadRes a

  ||| We reached the end of input.
  EOI         : ReadRes a

  ||| We got `n` bytes of data.
  Res         : (res : a) -> ReadRes a

%runElab derive "ReadRes" [Show,Eq]

export
Functor ReadRes where
  map f Interrupted = Interrupted
  map f NoData      = NoData
  map f Closed      = Closed
  map f EOI         = EOI
  map f (Res res)   = Res (f res)

export
Foldable ReadRes where
  foldr f v (Res r) = f r v
  foldr _ v _       = v

export
Traversable ReadRes where
  traverse f Interrupted = pure Interrupted
  traverse f NoData      = pure NoData
  traverse f Closed      = pure Closed
  traverse f EOI         = pure EOI
  traverse f (Res res)   = Res <$> f res

export
fromErr : Errno -> EPrim (ReadRes a)
fromErr err t =
  if      err == EAGAIN      then R NoData t
  else if err == EWOULDBLOCK then R NoData t
  else if err == EINTR       then R Interrupted t
  else if err == EPIPE       then R Closed t
  else                            E err t

--------------------------------------------------------------------------------
-- Read and Write Interfaces
--------------------------------------------------------------------------------

public export
record CPtr where
  constructor CP
  size : Bits32
  ptr  : AnyPtr

export
cptrOf1 : (0 a : Type) -> SizeOf a => Nat -> F1 World CPtr
cptrOf1 a n t =
  let sz := cast n * sizeof a
      p  := prim__malloc sz
   in CP sz (prim__malloc sz) # t

export %inline
cptrOf : HasIO io => (0 a : Type) -> SizeOf a => Nat -> io CPtr
cptrOf a = runIO . cptrOf1 a

export %inline
cptr1 : Nat -> F1 World CPtr
cptr1 = cptrOf1 Bits8

export %inline
cptr : HasIO io => Nat -> io CPtr
cptr = runIO . cptr1

export %inline
freePtr1 : CPtr -> F1' World
freePtr1 (CP _ p) = toF1 (prim__free p)

export %inline
freePtr : HasIO io => CPtr -> io ()
freePtr = runIO . freePtr1

public export
record Buf where
  constructor B
  size : Bits32
  buf  : Buffer

export %inline
buf : Bits32 -> F1 World Buf
buf sz t =
  let b # t := toF1 (prim__newBuf sz) t
   in B sz b # t

||| Interface for wrapping or converting a freshly allocated buffer
||| for reading, or an already allocated C-pointer for streaming
||| data (typically from a file descriptor).
|||
||| Please note that not all conversions are guaranteed to be
||| lossless. For instance, converting a buffer to a (UTF-8) string
||| will only be safe if the byte array does not end in the middle of
||| a codepoint consisting of several bytes.
public export
interface FromBuf a where
  fromBuf : Buf -> F1 World a

public export
0 EMBuffer : Type
EMBuffer = DPair Nat IOBuffer

public export
0 EBuffer : Type
EBuffer = DPair Nat IBuffer

export %inline
FromBuf Buf where
  fromBuf buf t = buf # t

export %inline
FromBuf EMBuffer where
  fromBuf (B sz buf) t = (cast sz ** unsafeMBuffer buf) # t

export %inline
FromBuf EBuffer where
  fromBuf (B sz buf) t = (cast sz ** unsafeMakeBuffer buf) # t

export %inline
FromBuf ByteString where
  fromBuf (B sz buf) t = unsafeByteString (cast sz) buf # t

export %inline
FromBuf String where
  fromBuf buf t =
    let (n ** ib) # t := fromBuf {a = EBuffer} buf t
     in toString ib 0 n # t

public export
0 ECArrayIO : Type -> Type
ECArrayIO t = (n ** CArrayIO n t)

||| Interface for converting a value for writing.
|||
||| We distinguis between three situations:
|||
|||   a) The value is converted to a `ByteString`. In this case
|||      the value can be directly written and the runtime will take
|||      care of collecting its memory.
|||
|||   b) The value is converted to a `CPtr`, which has been allocated
|||      elsewhere. We are not responsible for freeing the pointer as
|||      it might be reused for streaming.
public export
interface ToBuf a where
  unsafeToBuf : a -> Either CPtr ByteString

export %inline
ToBuf ByteString where
  unsafeToBuf = Right

export %inline
ToBuf String where
  unsafeToBuf = Right . fromString

export %inline
{n : _} -> ToBuf (IBuffer n) where
  unsafeToBuf buf = Right $ unsafeByteString n (unsafeGetBuffer buf)

export %inline
{n : _} -> ToBuf (MBuffer t n) where
  unsafeToBuf buf = Right $ unsafeByteString n (unsafeFromMBuffer buf)

export %inline
ToBuf CPtr where
  unsafeToBuf = Left

export %inline
{n : _} -> SizeOf a => ToBuf (CArray t n a) where
  unsafeToBuf arr =
    Left (CP (cast n * sizeof a) (unsafeUnwrap arr))

export %inline
SizeOf a => ToBuf (ECArrayIO a) where
  unsafeToBuf (_ ** arr) = unsafeToBuf arr

export
{n : _} -> SizeOf a => SetPtr a => ToBuf (Vect n a) where
  unsafeToBuf vs =
    run1 $ \t =>
     let sz      := cast n * sizeof a
         buf # t := ffi (prim__newBuf sz) t
         arr # t := malloc1 a n t
         _   # t := writeVect arr vs t
         _   # t := ffi (prim__copy_pb (unsafeUnwrap arr) buf sz) t
         _   # t := free1 arr t
      in Right (unsafeByteString (cast sz) buf) # t

export %inline
SizeOf a => SetPtr a => ToBuf (List a) where
  unsafeToBuf vs = unsafeToBuf (Vect.fromList vs)

--------------------------------------------------------------------------------
-- Streaming Interfaces
--------------------------------------------------------------------------------

public export
record Convert t where
  [noHints]
  constructor C
  0 source : Type
  {auto sof  : SizeOf source}
  {auto derf : Deref source}
  convert : source -> F1 World t

||| Interface for wrapping or converting a c-land pointer.
|||
||| This is useful for streaming data from a file descriptor.
||| Idris (garbage collected) values are generated by copying the given
||| number of bytes.
|||
||| Please note that not all conversions are guaranteed to be
||| lossless. For instance, converting a buffer to a (UTF-8) string
||| will only be safe if the byte array does not end in the middle of
||| a codepoint consisting of several bytes.
public export
interface FromPtr a where
  fromPtr : CPtr -> F1 World a

export %inline
FromPtr CPtr where
  fromPtr = (#)

export %inline
SizeOf a => FromPtr (ECArrayIO a) where
  fromPtr (CP sz ptr) t =
    (cast (sz `div` sizeof a) ** unsafeWrap ptr) # t

export
FromPtr EBuffer where
  fromPtr (CP sz32 ptr) t =
    let buf # t := toF1 (prim__newBuf sz32) t
        _   # t := toF1 (prim__copy_pb ptr buf sz32) t
     in (cast sz32 ** unsafeMakeBuffer buf) # t

export
FromPtr EMBuffer where
  fromPtr (CP sz32 ptr) t =
    let buf # t := toF1 (prim__newBuf sz32) t
        _   # t := toF1 (prim__copy_pb ptr buf sz32) t
     in (cast sz32 ** unsafeMBuffer buf) # t

export
FromPtr ByteString where
  fromPtr cp t =
    let (n ** ib) # t := fromPtr {a = EBuffer} cp t
     in BS n (fromIBuffer ib) # t

export
FromPtr String where
  fromPtr cp t =
    let (n ** ib) # t := fromPtr {a = EBuffer} cp t
     in toString ib 0 n # t

export
Convert t => FromPtr (List t) where
  fromPtr @{C src conv} cp t =
    let (n ** arr) # t := fromPtr {a = ECArrayIO src} cp t
     in values [] arr conv n t

export
SizeOf a => Deref a => FromPtr (List a) where
  fromPtr cp t =
    let (n ** arr) # t := fromPtr {a = ECArrayIO a} cp t
     in values [] arr (#) n t

export
FromBuf CPtr where
  fromBuf (B sz buf) t =
    let p     := prim__malloc sz
        _ # t := toF1 (prim__copy_bp buf p sz) t
     in CP sz p # t

export %inline
SizeOf a => FromBuf (ECArrayIO a) where
  fromBuf b t = let cp # t := fromBuf b t in fromPtr cp t

export
viaPtrFromBuf : FromPtr r => Buf -> F1 World r
viaPtrFromBuf b t =
  let cp # t := fromBuf b t
      r  # t := fromPtr cp t
      _  # t := freePtr1 cp t
   in r # t

export %inline
Convert t => FromBuf (List t) where
  fromBuf = viaPtrFromBuf
