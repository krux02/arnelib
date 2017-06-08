import macros, sequtils, algorithm, mersenne, ziggurat_normal_dist, math

## random numbers
## stuff ##

template offsetof*(Typ: typedesc; member: untyped): int =
  var dummy = cast[ptr Typ](nil)
  cast[int](dummy[].member.addr)

proc iotaSeq*[T: SomeNumber](length: T) : seq[T] =
  result.newSeq length.int
  for i in 0 ..< int(length):
    result[i] = T(i)
  
## sequence operations ##
  
proc newSeq*[T](length, capacity: Natural): seq[T] =
  assert(length <= capacity)
  result.newSeq(capacity)
  result.setLen(length)

proc cap*[T](s: seq[T]): Natural =
  cast[ptr tuple[length, capacity: Natural]](s).capacity

proc setCap*[T](s: var seq[T]; newCap: Natural): void =
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
  testSeq.setCap 5
  assert testSeq.len == 4 and testSeq.cap == 6
  testSeq.setCap 10
  assert testSeq.len == 4 and testSeq.cap >= 10
  
proc sorted*[T](data: seq[T]): seq[T] =
  data.sorted(cmp)
  
proc indices*[T](arg: seq[T]): auto =
  0 ..< len(arg)
proc indices*(node: NimNode): auto =
  0 ..< len(node)
  
proc mkString*[T](data : openarray[T]; before, sep, after: string) : string =
  result = before
  for i,x in data:
    if i != 0: result &= sep
    result &= $data[i]
  result &= after

proc mkString*[T](data : openarray[T]; sep: string) : string =
  mkString(data, "", sep, "")

## macro operations ##
  
macro debugAst*(ast: typed): untyped =
  echo ast.repr
  ast

proc newIdentDefs*(names : openarray[NimNode], tpe,val: NimNode): NimNode =
  result = nnkIdentDefs.newTree(names)
  result.add tpe,val

proc newVarSection*(node: varargs[NimNode]): NimNode =
  result = nnkVarSection.newTree(node)
  
proc newAsgn*(lhs,rhs: NimNode): NimNode =
  nnkAsgn.newTree(lhs,rhs)
  
proc newBracketExpr*(node: NimNode, args: openarray[NimNode]): NimNode =
  result = nnkBracketExpr.newTree(node)
  for arg in args:
    result.add args

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

proc indexOf*(data: string; value: char): int =
  for i, x in data:
    if x == value:
      return i
  return -1
   
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
  builder.data[^1]

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
  let insertionPoint = builder.data[^1].get(index)

  innerStmtList.expectKind nnkStmtList
  insertionPoint.expectKind nnkStmtList
  insertionPoint.del(insertionPoint.len)
  for stmt in innerStmtList:
    insertionPoint.add stmt
 
proc pushBlockStmt*(builder: var NimNodeBuilder): void =
  builder.insertionPoints.add(@[builder.stmtList.len, 1])

  builder.data[^1].add nnkBlockStmt.newTree(
    newEmptyNode(), newStmtList())

  builder.data.add(newStmtList())
  
proc pushForStmt*(builder: var NimNodeBuilder; loopVar, rangeVal: NimNode): void =
  builder.insertionPoints.add(@[builder.stmtList.len, 2])

  builder.data[^1].add nnkForStmt.newTree(
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
  # no way to escape the $ sign implemented. Should probably be $$.
  
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
    
  assert s"Hello, my name is $myName, I am $age years old. In five years I am ${age + 5}" ==
          "Hello, my name is Arne, I am 28 years old. In five years I am 33"

  ###############
  # ########### #
  # # cast of # #
  # ########### #
  ###############

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

proc echoTagIntern(procDef: NimNode; printArgs: bool): NimNode {.compileTime.} =
  procDef.expectKind nnkProcDef

  let name = procDef[0].repr
  let nameLit = newLit(name)
  let echoCall = newCall(ident"echo", newLit("<" & name)) 
  
  if printArgs:
    for i in 1 ..< len(procDef[3]):
      let identDefs = procDef[3][i]
      for j in 0 ..< identDefs.len-2:
        let identNode = identDefs[j]
        let nameLit = newLit($identNode.ident)
        echoCall.add newLit(" ")
        echoCall.add nameLit
        echoCall.add newLit("=\"")
        echoCall.add identNode
        echoCall.add newLit("\"")
        
  echoCall.add newLit(">")
  
  let beginStmt = quote do:
    `echoCall`
    defer:
      echo "</", `nameLit`, ">"
  
  result = procDef
  result[6].insert(0, beginStmt)


macro echoTag*(procDef: untyped): untyped = echoTagIntern(procDef, true)
macro echoTagNoArgs*(procDef: untyped): untyped = echoTagIntern(procDef, false)
  
if isMainModule:
  proc foobar(x,y: int; s: string = ""): int {. echoTag .} =
    if y == 0:
      x
    else:
      foobar(x+1, y-1, s)

  echo foobar(17,4, "abc")
  
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
# no export of generic implementation, because it creates too many false 
# posititives in completion
      
proc genRangeswap[Coll](data: var Coll; s0, s1, N: Natural): void =
  for i in 0 ..< N:
    swap(data[s0+i], data[s1+i])
    
proc genRotate[Coll](data: var Coll; first, middle, last: Natural): void =
  assert(0 <= first and first <= middle and middle < last and last <= data.len)
  if first == middle:
    return
    
  let
    N = middle - first
    M = last - middle
  
  if N < M:
    genRangeswap(data, first  , middle  , N  )
    genRotate(data, first+N, middle+N, last)
  else: # M >= N
    genRangeswap(data, first    , middle  , M )
    genRotate(data, first+M, middle, last)

proc rotate*(data: var string; first, middle, last: Natural): void =
  genRotate(data, first, middle, last)

proc rotate*(data: var string; middle: Natural): void =
  genRotate(data, 0, middle, data.len)
  
proc rotate*[T](data: var openarray[T]; first, middle, last: Natural): void =
  genRotate(data, first, middle, last)
  
proc rotate*[T](data: var openarray[T]; middle: Natural): void =
  genRotate(data, 0, middle, data.len)
  
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
  s0.rotate(3, 6, 10)
  s0.echoStringMarks(3,7,10)
  echo ""
  s1.echoStringMarks(3,5,10)
  s1.rotate(3, 5, 10)
  s1.echoStringMarks(3,8,10)
  echo ""
  s2.echoStringMarks(3,7,10)
  s2.rotate(3, 7, 10)  
  s2.echoStringMarks(3,6,10)

  namedEcho s0, s1, s2 

  
proc rangeUntilNode*(upper: int): NimNode {.compileTime.} =
  nnkInfix.newTree(ident"..<", newLit(0), newLit(upper))


##########################################################################################
###################################### zip iterators #####################################
##########################################################################################

## -- 2 -- ##

iterator zipIter*[T0,T1](arg0: openarray[T0]; arg1: openarray[T1]): tuple[v0:T0; v1:T1] =
  let high = min(high(arg0), high(arg1))

  for i in 0 .. high:
    yield(arg0[i], arg1[i])

iterator indexZipIter*[T0,T1](arg0: openarray[T0]; arg1: openarray[T1]): tuple[i: Natural; v0:T0; v1:T1] =
  let high = min(high(arg0), high(arg1))      

  for i in 0 .. high:
    yield(Natural(i), arg0[i], arg1[i])

iterator zipIter*[T0,T1,T2](
    arg0: openarray[T0]; arg1: openarray[T1]; arg2: openarray[T2]):
       tuple[v0:T0; v1:T1; v2:T2] =
         
  let high = min(high(arg0), high(arg1), high(arg2))

  for i in 0 .. high:
    yield(arg0[i], arg1[i], arg2[i])

iterator indexZipIter*[T0,T1,T2](
    arg0: openarray[T0]; arg1: openarray[T1]; arg2: openarray[T2]):
       tuple[i: Natural; v0:T0; v1:T1; v2:T2] =
         
  let high = min(high(arg0), high(arg1), high(arg2))
  for i in 0 .. high:
    yield(Natural(i), arg0[i], arg1[i], arg2[i])

iterator zipIter*[T0,T1,T2,T3](
    arg0: openarray[T0]; arg1: openarray[T1]; arg2: openarray[T2]; arg3: openarray[T3]):
       tuple[v0:T0; v1:T1; v2:T2; v3:T3] =
         
  let high = min(high(arg0), high(arg1), high(arg2), high(arg3))

  for i in 0 .. high:
    yield(arg0[i], arg1[i], arg2[i], arg3[i])

iterator indexZipIter*[T0,T1,T2,T3](
    arg0: openarray[T0]; arg1: openarray[T1]; arg2: openarray[T2]; arg3: openarray[T3]):
       tuple[i: Natural; v0:T0; v1:T1; v2:T2; v3:T3] =
         
  let high = min(high(arg0), high(arg1), high(arg2), high(arg3))
  for i in 0 .. high:
    yield(Natural(i), arg0[i], arg1[i], arg2[i], arg3[i])

when isMainModule:
  var data0 = @[10,20,30,40,50]
  var data1 = @["a", "b", "c"]

  for intVal,strVal in zipIter(data0, data1):
    echo strVal, " - ", intVal

  for i,intVal,strVal in indexZipIter(data0, data1):
    echo strVal, " - ", intVal

#[
macro genZipIter(numArgs: static[int]): untyped =
  result = quote do:
    iterator zipIter[T0,T1](arg0: openarray[T0]; arg1: openarray[T1]): tuple[v0:T0; v1:T1] =
      let high = min(high(arg0), high(arg1))

      for i in 0 .. high:
        yield(arg0[i], arg1[i])

    iterator indexZipIter[T0,T1](arg0: openarray[T0]; arg1: openarray[T1]): tuple[i: Natural; v0:T0; v1:T1] =
      let high = min(high(arg0), high(arg1))      

      for i in 0 .. high:
        yield(Natural(i), arg0[i], arg1[i])

  var genericsParamDefs = result[0][2][0]
  for i in 2 ..< numArgs:
    genericsParamDefs.insert(i, ident(s"T$i"))
  result[0][2][0] = genericsParamDefs
  result[1][2][0] = genericsParamDefs

  var resultTupleIdentDefs = result[0][3][0]

  for i in 2 ..< numArgs:
    resultTupleIdentDefs.add nnkIdentDefs.newTree(
      ident(s"v$i"),
      ident(s"T$i"),
      newEmptyNode()
    )

  result[0][3][0] = resultTupleIdentDefs
  
  var argumentsNode = result[0][3]

  for i in 2 ..< numArgs:
    let newNode = nnkIdentDefs.newTree(
      ident(s"arg$i"),
      newBracketExpr(ident"openArray", ident(s"T$i")),
      newEmptyNode()
    )
      
    argumentsNode.insert(i+1, newNode)

  result[0][3] = argumentsNode
  result[1][3] = argumentsNode
  
  echo result.repr
]#    



