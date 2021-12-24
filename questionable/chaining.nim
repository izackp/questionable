import std/options
import std/macros
import std/strformat
import std/importutils

proc unsafeGet*[T](self: var Option[T]): var T {.inline.} =
  ## Returns the value of a `some`. The behavior is undefined for `none`.
  ##
  ## **Note:** Use this only when you are **absolutely sure** the value is present
  ## (e.g. after checking with `isSome <#isSome,Option[T]>`_).
  ## Generally, using the `get proc <#get,Option[T]>`_ is preferred.
  assert self.isSome
  privateAccess(Option[T].type)
  self.val

func isSym(node: NimNode): bool =
  node.kind in {nnkSym, nnkOpenSymChoice, nnkClosedSymChoice}

func expectSym(node: NimNode) =
  node.expectKind({nnkSym, nnkOpenSymChoice, nnkClosedSymChoice})

macro expectReturnType(identifier: untyped, expression: untyped): untyped =
  let message =
    fmt"'{identifier}' doesn't have a return type, it can't be in a .? chain"
  quote do:
    when compiles(`expression`) and not compiles(typeof `expression`):
      {.error: `message`.}

template `.?`*(option: typed, identifier: untyped{nkIdent}): untyped =
  ## The `.?` chaining operator is used to safely access fields and call procs
  ## on Options or Results. The expression is only evaluated when the preceding
  ## Option or Result has a value.

  # chain is of shape: option.?identifier
  #expectReturnType(identifier, option.unsafeGet.identifier)
  when typeof(option.unsafeGet.identifier) is void:
    option -->? option.unsafeGet.identifier
  else:
    option ->? option.unsafeGet.identifier

macro `.?`*(option: typed, infix: untyped{nkInfix}): untyped =
  ## The `.?` chaining operator is used to safely access fields and call procs
  ## on Options or Results. The expression is only evaluated when the preceding
  ## Option or Result has a value.

  # chain is of shape: option.?left `operator` right
  let left = infix[1]
  infix[1] = quote do: `option`.?`left`
  #echo infix.treeRepr
  infix

macro `.?`*(option: typed, bracket: untyped{nkBracketExpr}): untyped =
  ## The `.?` chaining operator is used to safely access fields and call procs
  ## on Options or Results. The expression is only evaluated when the preceding
  ## Option or Result has a value.

  # chain is of shape: option.?left[right]
  let left = bracket[0]
  bracket[0] = quote do: `option`.?`left`
  #echo bracket.treeRepr
  bracket

macro `.?`*(option: typed, dot: untyped{nkDotExpr}): untyped =
  ## The `.?` chaining operator is used to safely access fields and call procs
  ## on Options or Results. The expression is only evaluated when the preceding
  ## Option or Result has a value.

  # chain is of shape: option.?left.right
  let left = dot[0]
  dot[0] = quote do: `option`.?`left`
  #echo dot.treeRepr
  dot

macro `.?`*(option: typed, call: untyped{nkCall}): untyped =
  ## The `.?` chaining operator is used to safely access fields and call procs
  ## on Options or Results. The expression is only evaluated when the preceding
  ## Option or Result has a value.

  let procedure = call[0]
  let astTree = if call.len == 1:
    # chain is of shape: option.?procedure()
    quote do: `option`.?`procedure`
  elif procedure.kind == nnkDotExpr:
    # chain is of shape: option.?left.right(arguments)
    let (left, right) = (procedure[0], procedure[1])
    call[0] = right
    call.insert(1, quote do: `option`.?`left`)
    call
  elif procedure.isSym and $procedure == "[]":
    # chain is of shape: option.?left[right] after semantic analysis
    let left = call[1]
    call[1] = quote do: `option`.?`left`
    call
  else:
    # chain is of shape: option.?procedure(arguments)
    call.insert(1, quote do: `option`.unsafeGet)
    quote do:
      expectReturnType(`procedure`, `call`)
      `option` ->? `call`
  #echo treeRepr(astTree)
  #echo astTree.repr
  #echo astTree.kind
  return astTree

macro `.?`*(option: typed, symbol: untyped): untyped =
  ## The `.?` chaining operator is used to safely access fields and call procs
  ## on Options or Results. The expression is only evaluated when the preceding
  ## Option or Result has a value.

  symbol.expectSym()
  let expression = ident($symbol)
  result = quote do: `option`.?`expression`
  #echo result.treeRepr
