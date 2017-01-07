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


dumpTree:
  node[0][1][2][3]

macro update[N](arg: NimNode; index: array[N, int]; value: untyped): untyped =
  var node = arg
  for i in 0 ..< index.len - 1:
    let lit = index[i]
    node = nnkBracketExpr.newTree(node, lit)

  let lastLit = index[index.len-1]
  
  result = quote do:
    replace(`node`, `lastLit`, toSeq(`value`))

  echo result.repr

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

  
macro test(): untyped =
  var foo = quote do:
    [1,2,3,4, @@(var x = 0)]

  iterator bar(): NimNode =
    for i in [1,2,3]:
      yield newLit(i)

  foo.update([0,0], bar())
  
#test()

    
macro foo1(): untyped =
  let sym0 = genSym()
  
  result = quote do:
    [`sym0`]

    
  iterator iter0(): NimNode =
    for i in 1 .. 3: yield newLit(i)
  
  result.update([0,0], iter0())
  
let x = foo1()
echo @x

proc recGenSymSubst(arg: NimNode; index: seq[int]; dst: var seq[tuple[sym: NimNode; index: seq[int]; node: NimNode]]): void =
  for i, node in arg:
    if node.kind == nnkPrefix and node[0] == ident"@@":
      let sym = genSym(nskLet, "sym" & $i)
      dst.add((sym: sym, index: index & i, node: node))
      arg[i] = sym
    else:
      node.recGenSymSubst(index & i, dst)
    
proc recGenSymSubst(arg: NimNode) : seq[tuple[sym: NimNode; index: seq[int]; node: NimNode]] =
  result.newSeq(0)
  arg.recGenSymSubst(@[], result)
      
macro superQuote(arg: untyped): untyped =
  echo arg.treeRepr
  result = arg
  echo arg.repr
  let tmp = result.recGenSymSubst

  for sym, index, node in tmp.items():
    # todo this needs some smartness:
    # the node is the node of an ast that needs to be compiled to an iterator
    result.update(index, node)
    
  echo result.repr

superQuote:
  [ @@(for i in 1 .. 3: yield newLit(i); yield newLit(7))]

