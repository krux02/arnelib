import macros

## sequence operations ##

proc newSeq*[T](length, capacity: Natural): seq[T] =
  assert(length <= capacity)
  result.newSeq(capacity)
  result.setLen(length)

proc cap*[T](s: seq[T]): Natural =
  cast[ptr tuple[length, capacity: Natural]](s).capacity

proc reserve*[T](s: var seq[T]; newCap: Natural): void =
  if newCap > s.cap:
    let oldLen = s.len
    s.setLen newCap
    s.setLen oldLen

proc data*[T](s: var seq[T]) : ptr T = 
  addr(s[0])
  
proc data*[N, T](s: var array[N, T]) : ptr T = 
  addr(s[0])
  
when isMainModule:
  var testSeq = newSeq[int](0, 3)
  assert testSeq.len == 0 and testSeq.cap == 3
  testSeq.add([1,2,3,4])
  assert testSeq.len == 4 and testSeq.cap == 6
  testSeq.reserve 5
  assert testSeq.len == 4 and testSeq.cap == 6
  testSeq.reserve 10
  assert testSeq.len == 4 and testSeq.cap >= 10
  

proc back*(node: NimNode): NimNode = node[node.len-1]
proc back*[T](data: seq[T]): T = data[high(data)]
proc back*[T](data: openarray[T]): T = data[high(data)]

proc head*(node: NimNode): NimNode = node[0]
proc head*[T](data: seq[T]): T = data[0]
proc head*[T](data: openarray[T]): T = data[0]

proc sorted*[T](data: seq[T]): seq[T] =
  data.sorted(cmp)

proc indices*[T](arg: seq[T]): auto =
  0 ..< len(arg)
proc indices*(node: NimNode): auto =
  0 ..< len(node)
  
proc mkString*[T](data : openarray[T]; before, sep, after: string) : string =
  result = before
  result &= $data[0]
  for i in 1 .. high(data):
    result &= sep
    result &= $data[i]
  result &= after

proc mkString*[T](data : openarray[T]; sep: string) : string =
  mkString(data, "", sep, "")

## macro operations ##
  
macro debugAst*(ast: typed): untyped =
  echo ast.repr
  ast
  
proc addAll*(dst, src: NimNode): NimNode {.discardable.} =
  for node in src:
    dst.add(node)
  dst

proc addAll*(dst: NimNode; src: openarray[NimNode]): NimNode {.discardable.} =
  for node in src:
    dst.add(node)
  dst

proc newIdentDefs*(names : openarray[NimNode], tpe,val: NimNode): NimNode =
  result = nnkIdentDefs.newTree(names)
  result.add tpe,val

proc newVarSection*(node: varargs[NimNode]): NimNode =
  result = nnkVarSection.newTree(node)
  
proc newAsgn*(lhs,rhs: NimNode): NimNode =
  nnkAsgn.newTree(lhs,rhs)
  
proc newBracketExpr*(node: NimNode, args: openarray[NimNode]): NimNode =
  result = nnkBracketExpr.newTree(node)
  result.addAll(args)

proc indexOf*(father,child: NimNode): int =
  for i in 0 ..< len(father):
    if father[i] == child:
      return i
  return -1

proc indexOf*[T](data: seq[T]; value: T): int =
  for i, x in data:
    if x == value:
      return i
  return -1
  
proc newDotExpr*(a,b,c: NimNode): NimNode =
  newDotExpr(a,b).newDotExpr(c)

proc newBracketExpr*(a,b: NimNode): NimNode =
  nnkBracketExpr.newTree(a,b)
  
proc newRangeUntil*(upper: int): NimNode {.compileTime.} =
  nnkInfix.newTree(ident"..<", newLit(0), newLit(upper))
  
type
  NimNodeBuilder* = object
    data: seq[NimNode]
    # since the nim runtime doesn't handle pointer types, I need to update the
    # nimnode at the insertion point on pop
    insertionPoints: seq[seq[int]]

proc newNimNodeBuilder*(root: NimNode = newStmtList()): NimNodeBuilder =
  result.data = @[root]
  result.insertionPoints = @[]

proc getResult*(builder: NimNodeBuilder): NimNode =
  assert(builder.data.len == 1)
  builder.data[0]
  
proc stmtList*(builder: NimNodeBuilder): NimNode =
  builder.data.back

proc root*(builder: NimNodeBuilder): NimNode = builder.data[0] 

proc get(dst: NimNode; index: seq[int]): NimNode =
  ## dst.get(@[1,2,3]) should be equivalent to dst[1][2][3]
  var it = dst
  for i in index:
    it = it[i]
    
  return it

proc pop*(builder: var NimNodeBuilder): NimNode {.discardable.} =
  let innerStmtList = builder.data.pop
  let index = builder.insertionPoints.pop
  let insertionPoint = builder.data.back.get(index)

  innerStmtList.expectKind nnkStmtList
  insertionPoint.expectKind nnkStmtList
  insertionPoint.del(insertionPoint.len)
  insertionPoint.addAll(innerStmtList)
 
proc pushBlockStmt*(builder: var NimNodeBuilder): void =
  builder.insertionPoints.add(@[builder.stmtList.len, 1])

  builder.data.back.add nnkBlockStmt.newTree(
    newEmptyNode(), newStmtList())

  builder.data.add(newStmtList())
  
proc pushForStmt*(builder: var NimNodeBuilder; loopVar, rangeVal: NimNode): void =
  builder.insertionPoints.add(@[builder.stmtList.len, 2])

  builder.data.back.add nnkForStmt.newTree(
    loopVar,
    rangeVal,
    newStmtList()
  )

  builder.data.add(newStmtList())
  
template blockBlock*(builder: var NimNodeBuilder, blk: untyped): void =
  builder.pushBlockStmt
  blk
  builder.pop

template forStmtBlock*(builder: var NimNodeBuilder; loopVar, rangeVal: NimNode, blk: untyped): NimNode =
  builder.pushForStmt
  blk
  builder.pop

## string interpolation
  
proc isIdentChar(c: char): bool =
  'A' <= c and c <= 'Z' or 'a' <= c and c <= 'z' or '0' <= c and c <= '9' or c == '_'

macro s*(arg: static[string]): string =
  # does not handle utf8 runes properly
  # pretents everything is ASCII 
  # no way to escape the $ sign. Should probably be $$.
  result = nnkStmtListExpr.newTree()
  let str = genSym(nskVar, "str")
  result.add quote do:
    var `str`: string = ""

  var i = 0
  var j = 0
  while true:
    while j < len(arg) and arg[j] != '$':
      j += 1

    let lit = newLit(arg[i..<j])
    result.add quote do:
      `str`.add(`lit`)
      
    if j == len(arg):    
      break

    var exprString : string
    
    if arg[j+1] == '{':
      j += 2
      i = j
      while j < len(arg) and arg[j] != '}':
        if arg[j] == '{':
          error "{ not allowed here"
        j += 1

      exprString = arg[i..<j]

      j += 1
    else:
      j += 1
      i = j
      while j < len(arg) and arg[j].isIdentChar:
        # does not deal with the fact that identifiers may not start or end on _,
        # also does not deal with the fact that the first char may not be a digit 
        j += 1
      exprString = arg[i..<j]

    let expr = parseExpr(exprString)
    result.add quote do:
      `str`.add($`expr`) ## a
      
    if j == len(arg):
      break
    
    i = j
  for i in 0 ..< result.len:
    # remove unnecessary stmtList wrapping
    # of each statement 
    result[i] = result[i][0]
    
  result.add str

## etc ##
  
proc joinValue*[T](a,b: T): T =
  ## assumes two arguments are the same, and just returns one of them
  ## fails when they are not the same
  assert(a == b)
  a
    
when isMainModule:  
  let 
    myName = "Arne"
    age    = 28
    
  assert s"Hello, my name is $myName, I am $age years old. In five years I am ${age + 5}" == "Hello, my name is Arne, I am 28 years old. In five years I am 33"

  ###############
  # ########### #
  # # cast of # #
  # ########### #
  ###############


import macros

macro castof*(sym:typed, t : typedesc): untyped =
  # introduce a new identifier with the same name as the input identifier
  # this identifier will have the type t, but hide sym
  let ident = newIdentNode($sym.symbol)
  result = quote do:
    (let `ident` = cast[`t`](`sym`); `sym` of `t`)

macro namedEcho*(x: typed, xs: varargs[typed]): untyped =
  let lit = newLit(x.repr & "=")
  let sepLit = newLit(" ")
  result = newCall(ident"echo", lit, x)

  for x in xs:
    let lit = newLit(x.repr & "=")
    result.add sepLit, lit, x
  
  echo result.repr
    
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

# gen prefix because of full generic implementation
# no export of generic implementation, because it casese too many false 
# posititives in completion
      
proc genRangeswap[Coll](data: var Coll; s0, s1, N: Natural): void =
  for i in 0 ..< N:
    swap(data[s0+i], data[s1+i])
    
proc genTransform[Coll](data: var Coll; first, middle, last: Natural): void =
  assert(0 <= first and first <= middle and middle < last and last <= data.len)
  if first == middle:
    return
    
  let
    N = middle - first
    M = last - middle
  
  if N < M:
    genRangeswap(data, first  , middle  , N  )
    genTransform(data, first+N, middle+N, last)
  else: # M >= N
    genRangeswap(data, first    , middle  , M )
    genTransform(data, first+M, middle, last)

proc transform(data: var string; first, middle, last: Natural): void =
  genTransform(data, first, middle, last)

proc transform(data: var string; middle: Natural): void =
  genTransform(data, 0, middle, data.len)
  
proc transform[T](data: var openarray[T]; first, middle, last: Natural): void =
  genTransform(data, first, middle, last)
  
proc transform[T](data: var openarray[T]; middle: Natural): void =
  genTransform(data, 0, middle, data.len)



  
when isMainModule:
  proc echoStringMarks(s: string, marks : varargs[int]) : void =
    for i, c in s:
      if i in marks:
        stdout.write "|"
      else:
        stdout.write " "
      stdout.write c

    if len(s) in marks:
      stdout.write  "|"
    echo ""

  var s0,s1,s2 = "xxxabcdefgxxx"

  s0.echoStringMarks(3,6,10)
  s0.transform(3, 6, 10)
  s0.echoStringMarks(3,7,10)
  echo ""
  s1.echoStringMarks(3,5,10)
  s1.transform(3, 5, 10)
  s1.echoStringMarks(3,8,10)
  echo ""
  s2.echoStringMarks(3,7,10)
  s2.transform(3, 7, 10)  
  s2.echoStringMarks(3,6,10)

  namedEcho s0, s1, s2 

  
proc rangeUntilNode*(upper: int): NimNode {.compileTime.} =
  nnkInfix.newTree(ident"..<", newLit(0), newLit(upper))
