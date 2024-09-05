module System.Callback

%default total

export %foreign "scheme:lock-object"
prim__lockobject : AnyPtr -> PrimIO ()

export %foreign "scheme:unlock-object"
prim__unlockobject : AnyPtr -> PrimIO ()

export %foreign "scheme:foreign-callable-code-object"
foreign_callable_code_object : AnyPtr -> AnyPtr

export %foreign "scheme:foreign-callable-entry-point"
foreign_callable_entry_point : AnyPtr -> AnyPtr

||| Locks a scheme object so it is no susceptible to garbage collection
||| when sent across the FFI. This is important when defining callback functions
||| to be used in C land.
export
lockPtr : HasIO io => AnyPtr -> io ()
lockPtr p = primIO $ prim__lockobject p

||| Reverts the effect of `lockPtr`
export %inline
unlockPtr : HasIO io => AnyPtr -> io ()
unlockPtr p = primIO $ prim__unlockobject p
