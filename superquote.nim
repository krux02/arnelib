import macros, sequtils

iterator pairs(arg: NimNode): tuple[key: int; value: NimNode] =
  var i = 0
  for child in arg:
    yield (i, child)
    inc i

proc replace(node: NimNode; index: int; subst: seq[NimNode]): void =
  node.del(index)
  for i, s in subst:
    node.insert(index + i, s)
    
proc recSearchAndReplace(tree: NimNode, node: NimNode, subst: seq[NimNode]): bool =
  for i, child in tree:
    if child == node:
      replace(tree, i, subst)
      return true
      
  for child in tree:
    if child.recSearchAndReplace(node, subst):
      return true
      
  return false

#dumpTree:
#  node[0][1][2][3]

#[
macro update[N](arg: NimNode; index: array[N, int]; value: untyped): untyped =
  var node = arg
  for i in 0 ..< index.len - 1:
    let lit = index[i]
    node = nnkBracketExpr.newTree(node, lit)

  let lastLit = index[index.len-1]
  
  result = quote do:
    replace(`node`, `lastLit`, toSeq(`value`))

  echo result.repr
]#

proc head(arg: seq[int]): int = arg[0]
proc tail(arg: seq[int]): seq[int] = arg[1..arg.high]

proc update(arg: NimNode; index: int; value: seq[NimNode]): void =
  arg.del(index)
  for i, node in value:
    arg.insert(index + i, node)

proc update(arg: NimNode; index: seq[int]; value: seq[NimNode]): void =
  if index.len > 1:
    update(arg[index.head], index.tail, value)
  else:
    update(arg, index.head, value)

#[  
macro test(): untyped =
  var foo = quote do:
    [1,2,3,4, @@(var x = 0)]

  iterator bar(): NimNode =
    for i in [1,2,3]:
      yield newLit(i)

  foo.update([0,0], bar())
]#

template makeNodeSeq(arg: untyped): untyped =
  iterator myIter(): NimNode =
    arg

  let s = toSeq(myIter())
  s

macro foo1(): untyped =
  let sym0 = genSym()
  
  result = quote do:
    [`sym0`]
    
  iterator iter0(): NimNode =
    for i in 1 .. 3: yield newLit(i)
  
  result.update(@[0,0], toSeq(iter0()))
  
let x = foo1()
echo @x

proc recGenSymSubst(arg: NimNode; index: seq[int]; dst: var seq[tuple[sym: NimNode; index: seq[int]; node: NimNode]]): void =
  for i, node in arg:
    if node.kind == nnkPrefix and node[0] == ident"@@":
      let sym = ident("sym" & $i)
      dst.add((sym: sym, index: index & i, node: node[1]))
      arg[i] = sym
    else:
      node.recGenSymSubst(index & i, dst)
    
proc recGenSymSubst(arg: NimNode) : seq[tuple[sym: NimNode; index: seq[int]; node: NimNode]] =
  result.newSeq(0)
  arg.recGenSymSubst(@[], result)

  
macro superQuote(arg: untyped): untyped =
  arg.expectKind nnkDo
  #echo arg.treeRepr
  
  var substAst = arg[6]
  let tmp = substAst.recGenSymSubst

  echo substAst.repr

  var updateCalls = newSeq[NimNode](0)

  let astSym = genSym(nskLet, "ast")
  
  for sym, index, node in tmp.items():
    # todo this needs some smartness:
    # the node is the node of an ast that needs to be compiled to an iterator
    ## result.update(index, node)

    let iter = genSym(nskIterator, "nodeIt")
    
    updateCalls.add quote do:
      iterator `iter`(): NimNode =
        `node`
        
      `astSym`.update(@`index`, toSeq(`iter`()))

  var xresult = newStmtList()

  for i in 0 ..< updateCalls.len:
    xresult.add(updateCalls[updateCalls.len - 1 - i])

  let macrosym = genSym(nskMacro, "mac")
    
  var result = quote do:
    macro `macrosym`(arg: untyped): untyped =
      echo "in inner generated macro"
      echo "arg: ", arg.repr
      
      let `astSym` = arg
      `xresult`

      return `astSym`

    `macrosym`(`substAst`)

  echo result.repr
#[
proc main(): void =
  let x = superQuote do:
    [ @@(for i in 1 .. 3: yield newLit(i); yield newLit(7)) ]

  #echo x
]#
#main()

macro mac109499(arg109501: untyped): untyped =
  echo "in inner generated macro"
  echo "arg: ", arg109501.repr
  let ast109497 = arg109501
  iterator nodeIt109498(): NimNode =
    for i in 1 .. 3: yield newLit(i)
    yield newLit(7)

  ast109497.update(@ [0, 0], toSeq(nodeIt109498()))
  return ast109497

mac109499:
  [sym0]


#[
template makeseq(arg: untyped): untyped =
  iterator myIter(): int =
    arg

  let s = toSeq(myIter())
  s

proc main(): void =
  let s = makeseq do:
    yield 1
    yield 2
    for i in 1 .. 3:
      yield i

  echo s
  
]#
