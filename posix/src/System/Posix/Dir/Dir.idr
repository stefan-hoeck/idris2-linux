module System.Posix.Dir.Dir

%default total

export
record Dir where
  constructor MkDir
  ptr : AnyPtr

export %inline
dirptr : Dir -> AnyPtr
dirptr = ptr

export %inline
wrapdir : AnyPtr -> Dir
wrapdir = MkDir
