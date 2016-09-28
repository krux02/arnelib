import macros

macro castof*(sym:typed, t : typedesc): expr =
  # introduce a new identifier with the same name as the input identifier
  # this identifier will have the type t, but hide sym
  let ident = newIdentNode($sym.symbol)
  result = quote do:
    (let `ident` = cast[`t`](`sym`); `sym` of `t`)

macro namedEcho*(x: typed): expr =
  let lit = newLit(x.repr & ": ")
  quote do:
    echo `lit`, `x`
    
if isMainModule:    
  type
    MyContainer[T] = object of RootObj
      data : seq[T]

    MyObject = object of RootObj
      banone : int

  var container1 = MyContainer[  int32](data: @[1'i32, 2,3,4,5])
  var container2 = MyContainer[float32](data: @[5'f32, 4,3,2,1]) 
  var banone : MyObject

  let all = @[
    (ptr RootObj)(container1.addr),
    container2.addr,
    banone.addr,
    nil
  ]

  for x in all:
    if x.castof(ptr MyObject):
      echo "it is Myobject ", x.banone
    elif x.castof(ptr MyContainer[int32]):
      echo "it is int32 ", x.data.len
    elif x.castof(ptr MyContainer[float32]):
      echo "it is float32 ", x.data.len
    else:
      echo "don't know the type"
      
