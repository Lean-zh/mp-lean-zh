/-
# `MetaM`

Lean 4 元编程 API 围绕着一系列单子（Monad）组织起来。主要有四个：

- `CoreM` 允许访问 **环境**，即程序当前点已声明或导入的事物集。
- `MetaM` 允许访问 **元变量语境**，即当前声明的元变量集及其赋值（如果有）。
- `TermElabM` 允许访问在繁饰过程中使用的各种信息。
- `TacticM` 允许访问当前目标列表。

这些单子相互扩展，因此 `MetaM` 操作也可以访问环境，而 `TermElabM` 计算可以使用元变量。还有其他单子不能很好地适应这个层次结构，例如`CommandElabM` 扩展了 `MetaM`，但与 `TermElabM` 没有扩展或被扩展的关系。

本章演示了 `MetaM` 单子中的许多有用操作。`MetaM` 特别重要，因为它允许我们为每个表达式赋予意义：环境（来自 `CoreM`）为 `Nat.zero` 或 `List.map` 等常量赋予意义，而元变量的语境为元变量和局部假设赋予意义。
-/

import Lean

open Lean Lean.Expr Lean.Meta

/-!
## 元变量

### 概述

`MetaM` 中的「Meta」指的是元变量，所以我们应该先讨论一下。Lean 用户通常不会与元变量进行太多交互--至少不是主动为之--但它们在元程序中随处可见。有两种方式看待它们：作为表达式中的洞或作为目标。

首先从目标角度来看。当我们在 Lean 中证明事物时，我们总是围绕目标进行操作，例如

```lean
n m : Nat
⊢ n + m = m + n
```

这些目标在内部由元变量表示。因此，每个元变量都有一个包含假设的**局部语境**（此处为`[n : Nat, m : Nat]`）和一个**目标类型**（此处为`n + m = m + n`）。元变量还有一个唯一的名称，比如 `m`，我们通常将它们呈现为 `?m`。

要证成目标，我们必须给出目标类型的表达式 `e`。该表达式可能包含来自元变量局部语境的自由变量fvar，但不包含其他变量。在内部，以这种方式证成目标相当于**指派**元变量，写作 `?m := e`。

元变量的第二个互补观点是它们表示表达式中的洞。例如，应用 `Eq.trans` 可能会生成两个如下所示的目标：

```lean
n m : Nat
⊢ n = ?x

n m : Nat
⊢ ?x = m
```

这里的 `?x` 是另一个元变量 -- 是两个目标类型中的一个空洞，在证明过程中会被填充。`?x` 的类型是 `Nat`，它的局部语境是 `[n : Nat, m : Nat]`。现在，如果我们通过 `rfl` 解决第一个目标，那么 `?x` 必须是 `n`，因此我们会赋值 `?x := n`。关键是，这同样会影响第二个目标：它的目标将被“更新”为 `n = m`（实际上并不是完全更新，后续会说明）。元变量 `?x` 在它出现的所有地方都代表相同的表达式。

### 通过元变量进行策略通信

策略通过元变量来传递当前的目标。为了理解这一点，我们来看一个简单（但稍显刻意）的证明例子：
-/

example {α} (a : α) (f : α → α) (h : ∀ a, f a = a) : f (f a) = a := by
  apply Eq.trans
  apply h
  apply h

/-!
进入策略模式后，我们的最终目标是生成一个类型为 `f (f a) = a` 的表达式，这个表达式可能会涉及假设 `α`、`a`、`f` 和 `h`。因此，Lean 生成了一个目标类型为 `f (f a) = a` 的元变量 `?m1`，它的局部语境包含了这些假设。这个元变量被传递给第一个 `apply` 策略作为当前目标。

`apply` 策略尝试应用 `Eq.trans` 并成功，生成了三个新的元变量：

```lean
...
⊢ f (f a) = ?b

...
⊢ ?b = a

...
⊢ α
```

我们称这些元变量为 `?m2`、`?m3` 和 `?b`。其中最后一个 `?b` 代表了传递性证明中的中间元素，并出现在 `?m2` 和 `?m3` 中。所有这些元变量的局部语境是相同的，因此我们省略它们。

创建了这些元变量后，`apply` 将进行以下赋值：

```lean
?m1 := @Eq.trans α (f (f a)) ?b a ?m2 ?m3
```

并报告说 `?m2`、`?m3` 和 `?b` 现在是当前的目标。

此时，第二个 `apply` 策略接手。它接收 `?m2` 作为当前目标，并将 `h` 应用于它。这成功了，并且策略赋值 `?m2 := h (f a)`。这个赋值意味着 `?b` 必须是 `f a`，因此策略也对 `?b := f a` 进行赋值。被赋值的元变量不再被视为开放目标，所以剩下的唯一目标是 `?m3`。

接着第三个 `apply` 策略开始执行。由于 `?b` 已经被赋值，`?m3` 的目标现在变成了 `f a = a`。再次应用 `h` 成功，策略将 `?m3 := h a` 进行赋值。

此时，所有元变量的赋值如下：

```lean
?m1 := @Eq.trans α (f (f a)) ?b a ?m2 ?m3
?m2 := h (f a)
?m3 := h a
?b  := f a
```

退出 `by` 块后，Lean 通过获取 `?m1` 的赋值并将每个元变量替换为它的赋值来构建最终的证明项。这最终得出以下结果：

```lean
@Eq.trans α (f (f a)) (f a) a (h (f a)) (h a)
```

这个例子还显示了元变量的两种视角 -- 作为表达式中的洞或作为目标 -- 是如何关联的：中间目标是最终证明项中的洞。

### 基本操作

让我们具体化这些概念。当我们在 `MetaM` 单子中操作时，我们可以读写访问包含当前声明的元变量信息的 `MetavarContext` 结构。每个元变量由一个 `MVarId`（一个唯一的 `Name`）标识。要创建一个新的元变量，我们使用 `Lean.Meta.mkFreshExprMVar`，其类型如下：

```lean
mkFreshExprMVar (type? : Option Expr) (kind := MetavarKind.natural)
    (userName := Name.anonymous) : MetaM Expr
```

其参数为：

- `type?`：新元变量的目标类型。如果为 `none`，目标类型为 `Sort ?u`，其中 `?u` 是一个宇宙层级元变量（这是一个特殊的元变量类别，用于宇宙层级，与我们一直称为「元变量」的表达式元变量不同）。
- `kind`：元变量的种类。参见[元变量种类](#metavariable-kinds)（通常默认值是正确的）。
- `userName`：新元变量的用户可见名称。这是当元变量出现在目标中时会显示的名称。与 `MVarId` 不同，这个名称不需要唯一。

返回的 `Expr` 始终是一个元变量。我们可以使用 `Lean.Expr.mvarId!` 来提取唯一的 `MVarId`。（可以说，`mkFreshExprMVar` 应该只返回 `MVarId`。）

新元变量的局部语境继承自当前的局部语境，更多细节将在下一节介绍。如果你想要提供不同的局部语境，可以使用 `Lean.Meta.mkFreshExprMVarAt`。

元变量最初是未赋值的。要为它们赋值，可以使用 `Lean.MVarId.assign`，其类型如下：

```lean
assign (mvarId : MVarId) (val : Expr) : MetaM Unit
```

这会使用赋值 `?mvarId := val` 来更新 `MetavarContext`。你必须确保 `mvarId` 尚未被赋值（或者旧的赋值与新的赋值是定义相等的）。你还必须确保赋值的值 `val` 具有正确的类型。这意味着 (a) `val` 必须具有 `mvarId` 的目标类型，并且 (b) `val` 必须只包含 `mvarId` 局部语境中的自由变量。

如果你 `#check Lean.MVarId.assign`，你会看到它的实际类型比我们上面显示的更通用：它适用于任何可以访问 `MetavarContext` 的单子。但 `MetaM` 是其中最重要的单子，所以在本章中，我们专门讨论 `assign` 和类似函数的类型。

要获取关于已声明的元变量的信息，使用 `Lean.MVarId.getDecl`。给定一个 `MVarId`，这会返回一个 `MetavarDecl` 结构。（如果没有声明给定 `MVarId` 的元变量，函数会抛出异常。）`MetavarDecl` 包含关于元变量的信息，例如其类型、局部语境和用户界面名称。这个函数有一些方便的变体，如 `Lean.MVarId.getType`。

要获取元变量的当前赋值（如果有），使用 `Lean.getExprMVarAssignment?`。要检查元变量是否已被赋值，使用 `Lean.MVarId.isAssigned`。然而，这些函数在策略代码中相对少用，因为我们通常更喜欢更强大的操作：`Lean.Meta.instantiateMVars` 类型为

```lean
instantiateMVars : Expr → MetaM Expr
```

给定一个表达式 `e`，`instantiateMVars` 用已赋值的值替换 `e` 中的任何已赋值元变量 `?m`。未赋值的元变量保持原样。

这个操作应该被广泛使用。当我们赋值一个元变量时，包含该元变量的现有表达式不会立即更新。这在例如我们匹配一个表达式以检查它是否是一个等式时会成为一个问题。如果没有 `instantiateMVars`，我们可能会错过表达式 `?m`，其中 `?m` 恰好被赋值为 `0 = n`，代表一个等式。换句话说，`instantiateMVars` 使我们的表达式与当前的元变量状态保持同步。

实例化元变量需要完整遍历输入表达式，所以它可能会有些昂贵。但如果输入表达式不包含任何元变量，`instantiateMVars` 基本上是免费的。由于这是常见情况，在大多数情况下广泛使用 `instantiateMVars` 是可以的。

在我们继续之前，这里有一个合成示例，展示了基本的元变量操作的使用。更自然的示例出现在接下来的部分中。
-/

#eval show MetaM Unit from do
  -- 创建两个新元变量，类型为 `Nat`
  let mvar1 ← mkFreshExprMVar (Expr.const ``Nat []) (userName := `mvar1)
  let mvar2 ← mkFreshExprMVar (Expr.const ``Nat []) (userName := `mvar2)
  -- 创建一个新元变量，类型为 `Nat → Nat`。`mkArrow` 函数创建了函数类型。
  let mvar3 ← mkFreshExprMVar (← mkArrow (.const ``Nat []) (.const ``Nat []))
    (userName := `mvar3)

  -- 定义一个辅助函数来打印这些元变量。
  let printMVars : MetaM Unit := do
    IO.println s!"  meta1: {← instantiateMVars mvar1}"
    IO.println s!"  meta2: {← instantiateMVars mvar2}"
    IO.println s!"  meta3: {← instantiateMVars mvar3}"

  IO.println "最初，所有的元变量都没被赋值："
  printMVars

  -- 赋值 `mvar1 : Nat := ?mvar3 ?mvar2`.
  mvar1.mvarId!.assign (.app mvar3 mvar2)
  IO.println "赋值mvar1之后："
  printMVars

  -- 赋值 `mvar2 : Nat := 0`.
  mvar2.mvarId!.assign (.const ``Nat.zero [])
  IO.println "赋值mvar2之后："
  printMVars

  -- 赋值 `mvar3 : Nat → Nat := Nat.succ`.
  mvar3.mvarId!.assign (.const ``Nat.succ [])
  IO.println "赋值mvar3之后："
  printMVars
-- 最初，所有的元变量都没被赋值：
--   meta1: ?_uniq.1
--   meta2: ?_uniq.2
--   meta3: ?_uniq.3
-- 赋值mvar1之后：
--   meta1: ?_uniq.3 ?_uniq.2
--   meta2: ?_uniq.2
--   meta3: ?_uniq.3
-- 赋值mvar2之后：
--   meta1: ?_uniq.3 Nat.zero
--   meta2: Nat.zero
--   meta3: ?_uniq.3
-- 赋值mvar3之后：
--   meta1: Nat.succ Nat.zero
--   meta2: Nat.zero
--   meta3: Nat.succ

/-!
### 局部语境

考虑表达式 `e`，它引用了唯一名称为 `h` 的自由变量：

```lean
e := .fvar (FVarId.mk `h)
```

这个表达式的类型是什么？答案取决于解释 `e` 的局部语境。一个局部语境可能声明 `h` 是类型为 `Nat` 的局部假设；另一个局部语境可能声明 `h` 是值为 `List.map` 的局部定义。

因此，表达式只有在为其设计的局部语境中解释时才有意义。如我们所见，每个元变量都有其自己的局部语境。因此，原则上，操作表达式的函数应该有一个附加的 `MVarId` 参数，指定解释表达式的目标。

这会很麻烦，所以 Lean 采用了稍微不同的方式。在 `MetaM` 中，我们始终可以访问一个环境局部语境，可以通过 `Lean.getLCtx` 函数获得，类型为：

```lean
getLCtx : MetaM LocalContext
```

所有涉及自由变量的操作都使用这个环境局部语境。

这种设置的缺点是我们始终需要更新环境局部语境以匹配当前处理的目标。为此，我们使用 `Lean.MVarId.withContext`，类型为

```lean
withContext (mvarId : MVarId) (c : MetaM α) : MetaM α
```

这个函数接受一个元变量 `mvarId` 和一个 `MetaM` 计算过程 `c`，功能是，设置环境语境为 `mvarId` 的局部语境，而后执行 `c`。典型的用例如下：

```lean
def someTactic (mvarId : MVarId) ... : ... :=
  mvarId.withContext do
    ...
```

策略接收当前目标作为元变量 `mvarId`，并立即设置当前局部语境。`do` 块内的任何操作都会使用 `mvarId` 的局部语境。

一旦我们正确设置了局部语境，我们就可以操作自由变量。与元变量类似，自由变量由 `FVarId`（一个唯一的 `Name`）标识。基本操作包括：

- `Lean.FVarId.getDecl : FVarId → MetaM LocalDecl` 获取局部假设的声明。与元变量一样，`LocalDecl` 包含所有关于局部假设的信息，例如其类型和用户界面名称。
- `Lean.Meta.getLocalDeclFromUserName : Name → MetaM LocalDecl` 获取给定用户界面名称的局部假设的声明。如果有多个这样的假设，返回最底部的那个。如果没有，抛出异常。

我们还可以使用 `LocalContext` 的 `ForIn` 实例在局部语境中的所有假设中迭代。典型模式如下：

```lean
for ldecl in ← getLCtx do
  if ldecl.isImplementationDetail then
    continue
  -- do something with the ldecl
```

循环在语境中的每个 `LocalDecl` 中迭代。`isImplementationDetail` 检查会跳过作为「实现细节」的局部假设，意味着它们是由 Lean 或策略为了记账引入的。它们不会显示给用户，策略应忽略它们。

此时，我们可以构建 `assumption` 策略的 `MetaM` 部分：
-/

def myAssumption (mvarId : MVarId) : MetaM Bool := do
  -- 检查 `mvarId` 是否尚未被赋值。
  mvarId.checkNotAssigned `myAssumption
  -- 使用 `mvarId` 的局部语境。
  mvarId.withContext do
    -- 目标 target 是 `mvarId` 的类型。
    let target ← mvarId.getType
    -- 对局部语境中的每个假设：
    for ldecl in ← getLCtx do
      -- 如果假设是「实现细节」，那么跳过。
      if ldecl.isImplementationDetail then
        continue
      -- 如果假设的类型定义等价于目标类型，那么：
      if ← isDefEq ldecl.type target then
        -- 使用局部假设来证明目标。
        mvarId.assign ldecl.toExpr
        -- 停止并返回 true。
        return true
    -- 如果没找到任何合适的假设，返回false。
    return false

/-
`myAssumption` 策略中使用了三个我们之前没有见过的函数：

- `Lean.MVarId.checkNotAssigned`：检查一个元变量是否尚未被赋值。`myAssumption` 参数是当前策略的名称，用于生成更友好的错误消息。
- `Lean.Meta.isDefEq`：检查两个定义是否在定义上相等。详细信息请参见[定义等价](#定义等价)部分。
- `Lean.LocalDecl.toExpr`：是一个辅助函数，用于构建对应于局部假设的 `fvar` 表达式。

### 延迟赋值

上述关于元变量赋值的讨论有一个遗漏：实际上有两种方式可以为元变量赋值。我们已经看到了一般的赋值方式，另一种称为**延迟赋值**（Delayed Assignments）。

这里我们不会详细讨论延迟赋值，因为它们对于编写策略并不常用。如果你想了解更多信息，可以参阅 Lean 标准库中的 `MetavarContext.lean` 文件中的注释。不过，它们带来了两个需要注意的复杂问题。

首先，延迟赋值使得 `Lean.MVarId.isAssigned` 和 `getExprMVarAssignment?` 成为可能导致问题的函数。这些函数只检查常规的赋值，因此你可能还需要使用 `Lean.MVarId.isDelayedAssigned` 和 `Lean.Meta.getDelayedMVarAssignment?`。

其次，延迟赋值打破了一种直观的约束。你可能假设在 `instantiateMVars` 的输出中仍然存在的元变量都是未赋值的，因为已赋值的元变量应该已经被替换掉了。但延迟赋值的元变量只有在其赋值的值不包含未赋值的元变量时才能被替换。因此，即使在 `instantiateMVars` 之后，延迟赋值的元变量仍然可能出现在表达式中。

### 元变量深度

元变量深度也是一个较为小众的特性，但有时会派上用场。每个元变量都有一个*深度*（一个自然数），并且 `MetavarContext` 也有一个相应的深度。Lean 只有在元变量的深度等于当前 `MetavarContext` 的深度时才会为其赋值。新创建的元变量继承 `MetavarContext` 的深度，因此默认情况下，每个元变量都是可赋值的。

这种机制在某些策略需要一些临时元变量，并且需要确保其他非临时元变量不会被赋值时会很有用。为了实现这一点，策略可以按照以下步骤进行：

1. 保存当前的 `MetavarContext`。
2. 增加 `MetavarContext` 的深度。
3. 执行必要的计算，可能会创建和赋值元变量。新创建的元变量位于当前 `MetavarContext` 的深度，因此可以被赋值。而旧的元变量位于较低的深度，因此不能被赋值。
4. 恢复保存的 `MetavarContext`，从而清除所有临时元变量并重置 `MetavarContext` 的深度。

这种模式封装在 `Lean.Meta.withNewMCtxDepth` 中。

### Metavariable Depth

Metavariable depth is also a niche feature, but one that is occasionally useful.
Any metavariable has a *depth* (a natural number), and a `MetavarContext` has a
corresponding depth as well. Lean only assigns a metavariable if its depth is
equal to the depth of the current `MetavarContext`. Newly created metavariables
inherit the `MetavarContext`'s depth, so by default every metavariable is
assignable.

This setup can be used when a tactic needs some temporary metavariables and also
needs to make sure that other, non-temporary metavariables will not be assigned.
To ensure this, the tactic proceeds as follows:

1. Save the current `MetavarContext`.
2. Increase the depth of the `MetavarContext`.
3. Perform whatever computation is necessary, possibly creating and assigning
   metavariables. Newly created metavariables are at the current depth of the
   `MetavarContext` and so can be assigned. Old metavariables are at a lower
   depth, so cannot be assigned.
4. Restore the saved `MetavarContext`, thereby erasing all the temporary
   metavariables and resetting the `MetavarContext` depth.

This pattern is encapsulated in `Lean.Meta.withNewMCtxDepth`.


## Computation

Computation is a core concept of dependent type theory. The terms `2`, `Nat.succ
1` and `1 + 1` are all "the same" in the sense that they compute the same value.
We call them *definitionally equal*. The problem with this, from a
metaprogramming perspective, is that definitionally equal terms may be
represented by entirely different expressions, but our users would usually
expect that a tactic which works for `2` also works for `1 + 1`. So when we
write our tactics, we must do additional work to ensure that definitionally
equal terms are treated similarly.

### Full Normalisation

The simplest thing we can do with computation is to bring a term into normal
form. With some exceptions for numeric types, the normal form of a term `t` of
type `T` is a sequence of applications of `T`'s constructors. E.g. the normal
form of a list is a sequence of applications of `List.cons` and `List.nil`.

The function that normalises a term (i.e. brings it into normal form) is
`Lean.Meta.reduce` with type signature

```lean
reduce (e : Expr) (explicitOnly skipTypes skipProofs := true) : MetaM Expr
```

We can use it like this:
-/

def someNumber : Nat := (· + 2) $ 3

#eval Expr.const ``someNumber []
-- Lean.Expr.const `someNumber []

#eval reduce (Expr.const ``someNumber [])
-- Lean.Expr.lit (Lean.Literal.natVal 5)

/-!
Incidentally, this shows that the normal form of a term of type `Nat` is not
always an application of the constructors of `Nat`; it can also be a literal.
Also note that `#eval` can be used not only to evaluate a term, but also to
execute a `MetaM` program.

The optional arguments of `reduce` allow us to skip certain parts of an
expression. E.g. `reduce e (explicitOnly := true)` does not normalise any
implicit arguments in the expression `e`. This yields better performance: since
normal forms can be very big, it may be a good idea to skip parts of an
expression that the user is not going to see anyway.

The `#reduce` command is essentially an application of `reduce`:
-/

#reduce someNumber
-- 5

/-!
### Transparency

An ugly but important detail of Lean 4 metaprogramming is that any given
expression does not have a single normal form. Rather, it has a normal form up
to a given *transparency*.

A transparency is a value of `Lean.Meta.TransparencyMode`, an enumeration with
four values: `reducible`, `instances`, `default` and `all`. Any `MetaM`
computation has access to an ambient `TransparencyMode` which can be obtained
with `Lean.Meta.getTransparency`.

The current transparency determines which constants get unfolded during
normalisation, e.g. by `reduce`. (To unfold a constant means to replace it with
its definition.) The four settings unfold progressively more constants:

- `reducible`: unfold only constants tagged with the `@[reducible]` attribute.
  Note that `abbrev` is a shorthand for `@[reducible] def`.
- `instances`: unfold reducible constants and constants tagged with the
  `@[instance]` attribute. Again, the `instance` command is a shorthand for
  `@[instance] def`.
- `default`: unfold all constants except those tagged as `@[irreducible]`.
- `all`: unfold all constants, even those tagged as `@[irreducible]`.

The ambient transparency is usually `default`. To execute an operation with a
specific transparency, use `Lean.Meta.withTransparency`. There are also
shorthands for specific transparencies, e.g. `Lean.Meta.withReducible`.

Putting everything together for an example (where we use `Lean.Meta.ppExpr` to
pretty-print an expression): -/

def traceConstWithTransparency (md : TransparencyMode) (c : Name) :
    MetaM Format := do
  ppExpr (← withTransparency md $ reduce (.const c []))

@[irreducible] def irreducibleDef : Nat      := 1
def                defaultDef     : Nat      := irreducibleDef + 1
abbrev             reducibleDef   : Nat      := defaultDef + 1

/-!
We start with `reducible` transparency, which only unfolds `reducibleDef`:
-/

#eval traceConstWithTransparency .reducible ``reducibleDef
-- defaultDef + 1

/-!
If we repeat the above command but let Lean print implicit arguments as well,
we can see that the `+` notation amounts to an application of the `hAdd`
function, which is a member of the `HAdd` typeclass:
-/

set_option pp.explicit true
#eval traceConstWithTransparency .reducible ``reducibleDef
-- @HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) defaultDef 1

/-!
When we reduce with `instances` transparency, this applications is unfolded and
replaced by `Nat.add`:
-/

#eval traceConstWithTransparency .instances ``reducibleDef
-- Nat.add defaultDef 1

/-!
With `default` transparency, `Nat.add` is unfolded as well:
-/

#eval traceConstWithTransparency .default ``reducibleDef
-- Nat.succ (Nat.succ irreducibleDef)

/-!
And with `TransparencyMode.all`, we're finally able to unfold `irreducibleDef`:
-/

#eval traceConstWithTransparency .all ``reducibleDef
-- 3

/-!
The `#eval` commands illustrate that the same term, `reducibleDef`, can have a
different normal form for each transparency.

Why all this ceremony? Essentially for performance: if we allowed normalisation
to always unfold every constant, operations such as type class search would
become prohibitively expensive. The tradeoff is that we must choose the
appropriate transparency for each operation that involves normalisation.


### Weak Head Normalisation

Transparency addresses some of the performance issues with normalisation. But
even more important is to recognise that for many purposes, we don't need to
fully normalise terms at all. Suppose we are building a tactic that
automatically splits hypotheses of the type `P ∧ Q`. We might want this tactic
to recognise a hypothesis `h : X` if `X` reduces to `P ∧ Q`. But if `P`
additionally reduces to `Y ∨ Z`, the specific `Y` and `Z` do not concern us.
Reducing `P` would be unnecessary work.

This situation is so common that the fully normalising `reduce` is in fact
rarely used. Instead, the normalisation workhorse of Lean is `whnf`, which
reduces an expression to *weak head normal form* (WHNF).

Roughly speaking, an expression `e` is in weak-head normal form when it has the
form

```text
e = f x₁ ... xₙ   (n ≥ 0)
```

and `f` cannot be reduced (at the current transparency). To conveniently check
the WHNF of an expression, we define a function `whnf'`, using some functions
that will be discussed in the Elaboration chapter.
-/

open Lean.Elab.Term in
def whnf' (e : TermElabM Syntax) : TermElabM Format := do
  let e ← elabTermAndSynthesize (← e) none
  ppExpr (← whnf e)

/-!
Now, here are some examples of expressions in WHNF.

Constructor applications are in WHNF (with some exceptions for numeric types):
-/

#eval whnf' `(List.cons 1 [])
-- [1]

/-!
The *arguments* of an application in WHNF may or may not be in WHNF themselves:
-/

#eval whnf' `(List.cons (1 + 1) [])
-- [1 + 1]

/-!
Applications of constants are in WHNF if the current transparency does not
allow us to unfold the constants:
-/

#eval withTransparency .reducible $ whnf' `(List.append [1] [2])
-- List.append [1] [2]

/-!
Lambdas are in WHNF:
-/

#eval whnf' `(λ x : Nat => x)
-- fun x => x

/-!
Foralls are in WHNF:
-/

#eval whnf' `(∀ x, x > 0)
-- ∀ (x : Nat), x > 0

/-!
Sorts are in WHNF:
-/

#eval whnf' `(Type 3)
-- Type 3

/-!
Literals are in WHNF:
-/

#eval whnf' `((15 : Nat))
-- 15

/-!
Here are some more expressions in WHNF which are a bit tricky to test:

```lean
?x 0 1  -- Assuming the metavariable `?x` is unassigned, it is in WHNF.
h 0 1   -- Assuming `h` is a local hypothesis, it is in WHNF.
```

On the flipside, here are some expressions that are not in WHNF.

Applications of constants are not in WHNF if the current transparency allows us
to unfold the constants:
-/

#eval whnf' `(List.append [1])
-- fun x => 1 :: List.append [] x

/-!
Applications of lambdas are not in WHNF:
-/

#eval whnf' `((λ x y : Nat => x + y) 1)
-- `fun y => 1 + y`

/-!
`let` bindings are not in WHNF:
-/

#eval whnf' `(let x : Nat := 1; x)
-- 1

/-!
And again some tricky examples:

```lean
?x 0 1 -- Assuming `?x` is assigned (e.g. to `Nat.add`), its application is not
          in WHNF.
h 0 1  -- Assuming `h` is a local definition (e.g. with value `Nat.add`), its
          application is not in WHNF.
```

Returning to the tactic that motivated this section, let us write a function
that matches a type of the form `P ∧ Q`, avoiding extra computation. WHNF
makes it easy:
-/

def matchAndReducing (e : Expr) : MetaM (Option (Expr × Expr)) := do
  match ← whnf e with
  | (.app (.app (.const ``And _) P) Q) => return some (P, Q)
  | _ => return none

/-
By using `whnf`, we ensure that if `e` evaluates to something of the form `P
∧ Q`, we'll notice. But at the same time, we don't perform any unnecessary
computation in `P` or `Q`.

However, our 'no unnecessary computation' mantra also means that if we want to
perform deeper matching on an expression, we need to use `whnf` multiple times.
Suppose we want to match a type of the form `P ∧ Q ∧ R`. The correct way to do
this uses `whnf` twice:
-/

def matchAndReducing₂ (e : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  match ← whnf e with
  | (.app (.app (.const ``And _) P) e') =>
    match ← whnf e' with
    | (.app (.app (.const ``And _) Q) R) => return some (P, Q, R)
    | _ => return none
  | _ => return none

/-!
This sort of deep matching up to computation could be automated. But until
someone builds this automation, we have to figure out the necessary `whnf`s
ourselves.


### 定义等价

As mentioned, definitional equality is equality up to computation. Two
expressions `t` and `s` are definitionally equal or *defeq* (at the current
transparency) if their normal forms (at the current transparency) are equal.

To check whether two expressions are defeq, use `Lean.Meta.isDefEq` with type
signature

```lean
isDefEq : Expr → Expr → MetaM Bool
```

Even though definitional equality is defined in terms of normal forms, `isDefEq`
does not actually compute the normal forms of its arguments, which would be very
expensive. Instead, it tries to "match up" `t` and `s` using as few reductions
as possible. This is a necessarily heuristic endeavour and when the heuristics
misfire, `isDefEq` can become very expensive. In the worst case, it may have to
reduce `s` and `t` so often that they end up in normal form anyway. But usually
the heuristics are good and `isDefEq` is reasonably fast.

If expressions `t` and `u` contain assignable metavariables, `isDefEq` may
assign these metavariables to make `t` defeq to `u`. We also say that `isDefEq`
*unifies* `t` and `u`; such unification queries are sometimes written `t =?= u`.
For instance, the unification `List ?m =?= List Nat` succeeds and assigns `?m :=
Nat`. The unification `Nat.succ ?m =?= n + 1` succeeds and assigns `?m := n`.
The unification `?m₁ + ?m₂ + ?m₃ =?= m + n - k` fails and no metavariables are
assigned (even though there is a 'partial match' between the expressions).

Whether `isDefEq` considers a metavariable assignable is determined by two
factors:

1. The metavariable's depth must be equal to the current `MetavarContext` depth.
   See the [Metavariable Depth section](#metavariable-depth).
2. Each metavariable has a *kind* (a value of type `MetavarKind`) whose sole
   purpose is to modify the behaviour of `isDefEq`. Possible kinds are:
   - Natural: `isDefEq` may freely assign the metavariable. This is the default.
   - Synthetic: `isDefEq` may assign the metavariable, but avoids doing so if
     possible. For example, suppose `?n` is a natural metavariable and `?s` is a
     synthetic metavariable. When faced with the unification problem
     `?s =?= ?n`, `isDefEq` assigns `?n` rather than `?s`.
   - Synthetic opaque: `isDefEq` never assigns the metavariable.


## Constructing Expressions

In the previous chapter, we saw some primitive functions for building
expressions: `Expr.app`, `Expr.const`, `mkAppN` and so on. There is nothing
wrong with these functions, but the additional facilities of `MetaM` often
provide more convenient ways.


### Applications

When we write regular Lean code, Lean helpfully infers many implicit arguments
and universe levels. If it did not, our code would look rather ugly: -/

def appendAppend (xs ys : List α) := (xs.append ys).append xs

set_option pp.all true in
set_option pp.explicit true in
#print appendAppend
-- def appendAppend.{u_1} : {α : Type u_1} → List.{u_1} α → List.{u_1} α → List.{u_1} α :=
-- fun {α : Type u_1} (xs ys : List.{u_1} α) => @List.append.{u_1} α (@List.append.{u_1} α xs ys) xs

/-!
The `.{u_1}` suffixes are universe levels, which must be given for every
polymorphic constant. And of course the type `α` is passed around everywhere.

Exactly the same problem occurs during metaprogramming when we construct
expressions. A hand-made expression representing the right-hand side of the
above definition looks like this:
-/

def appendAppendRHSExpr₁ (u : Level) (α xs ys : Expr) : Expr :=
  mkAppN (.const ``List.append [u])
    #[α, mkAppN (.const ``List.append [u]) #[α, xs, ys], xs]

/-!
Having to specify the implicit arguments and universe levels is annoying and
error-prone. So `MetaM` provides a helper function which allows us to omit
implicit information: `Lean.Meta.mkAppM` of type

```lean
mkAppM : Name → Array Expr → MetaM Expr
```

Like `mkAppN`, `mkAppM` constructs an application. But while `mkAppN` requires
us to give all universe levels and implicit arguments ourselves, `mkAppM` infers
them. This means we only need to provide the explicit arguments, which makes for
a much shorter example:
-/

def appendAppendRHSExpr₂ (xs ys : Expr) : MetaM Expr := do
  mkAppM ``List.append #[← mkAppM ``List.append #[xs, ys], xs]

/-!
Note the absence of any `α`s and `u`s. There is also a variant of `mkAppM`,
`mkAppM'`, which takes an `Expr` instead of a `Name` as the first argument,
allowing us to construct applications of expressions which are not constants.

However, `mkAppM` is not magic: if you write `mkAppM ``List.append #[]`, you
will get an error at runtime. This is because `mkAppM` tries to determine what
the type `α` is, but with no arguments given to `append`, `α` could be anything,
so `mkAppM` fails.

Another occasionally useful variant of `mkAppM` is `Lean.Meta.mkAppOptM` of type

```lean
mkAppOptM : Name → Array (Option Expr) → MetaM Expr
```

Whereas `mkAppM` always infers implicit and instance arguments and always
requires us to give explicit arguments, `mkAppOptM` lets us choose freely which
arguments to provide and which to infer. With this, we can, for example, give
instances explicitly, which we use in the following example to give a
non-standard `Ord` instance.
-/

def revOrd : Ord Nat where
  compare x y := compare y x

def ordExpr : MetaM Expr := do
  mkAppOptM ``compare #[none, Expr.const ``revOrd [], mkNatLit 0, mkNatLit 1]

#eval format <$> ordExpr
-- Ord.compare.{0} Nat revOrd
--   (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))
--   (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))

/-!
Like `mkAppM`, `mkAppOptM` has a primed variant `Lean.Meta.mkAppOptM'` which
takes an `Expr` instead of a `Name` as the first argument. The file which
contains `mkAppM` also contains various other helper functions, e.g. for making
list literals or `sorry`s.


### Lambdas and Foralls

Another common task is to construct expressions involving `λ` or `∀` binders.
Suppose we want to create the expression `λ (x : Nat), Nat.add x x`. One way is
to write out the lambda directly:
-/

def doubleExpr₁ : Expr :=
  .lam `x (.const ``Nat []) (mkAppN (.const ``Nat.add []) #[.bvar 0, .bvar 0])
    BinderInfo.default

#eval ppExpr doubleExpr₁
-- fun x => Nat.add x x

/-!
This works, but the use of `bvar` is highly unidiomatic. Lean uses a so-called
*locally closed* variable representation. This means that all but the
lowest-level functions in the Lean API expect expressions not to contain 'loose
`bvar`s', where a `bvar` is loose if it is not bound by a binder in the same
expression. (Outside of Lean, such variables are usually called 'free'. The name
`bvar` -- 'bound variable' -- already indicates that `bvar`s are never supposed
to be free.)

As a result, if in the above example we replace `mkAppN` with the slightly
higher-level `mkAppM`, we get a runtime error. Adhering to the locally closed
convention, `mkAppM` expects any expressions given to it to have no loose bound
variables, and `.bvar 0` is precisely that.

So instead of using `bvar`s directly, the Lean way is to construct expressions
with bound variables in two steps:

1. Construct the body of the expression (in our example: the body of the
   lambda), using temporary local hypotheses (`fvar`s) to stand in for the bound
   variables.
2. Replace these `fvar`s with `bvar`s and, at the same time, add the
   corresponding lambda binders.

This process ensures that we do not need to handle expressions with loose
`bvar`s at any point (except during step 2, which is performed 'atomically' by a
bespoke function). Applying the process to our example:

-/

def doubleExpr₂ : MetaM Expr :=
  withLocalDecl `x BinderInfo.default (.const ``Nat []) λ x => do
    let body ← mkAppM ``Nat.add #[x, x]
    mkLambdaFVars #[x] body

#eval show MetaM _ from do
  ppExpr (← doubleExpr₂)
-- fun x => Nat.add x x

/-!
There are two new functions. First, `Lean.Meta.withLocalDecl` has type

```lean
withLocalDecl (name : Name) (bi : BinderInfo) (type : Expr) (k : Expr → MetaM α) : MetaM α
```

Given a variable name, binder info and type, `withLocalDecl` constructs a new
`fvar` and passes it to the computation `k`. The `fvar` is available in the local
context during the execution of `k` but is deleted again afterwards.

The second new function is `Lean.Meta.mkLambdaFVars` with type (ignoring some
optional arguments)

```
mkLambdaFVars : Array Expr → Expr → MetaM Expr
```

This function takes an array of `fvar`s and an expression `e`. It then adds one
lambda binder for each `fvar` `x` and replaces every occurrence of `x` in `e`
with a bound variable corresponding to the new lambda binder. The returned
expression does not contain the `fvar`s any more, which is good since they
disappear after we leave the `withLocalDecl` context. (Instead of `fvar`s, we
can also give `mvar`s to `mkLambdaFVars`, despite its name.)

Some variants of the above functions may be useful:

- `withLocalDecls` declares multiple temporary `fvar`s.
- `mkForallFVars` creates `∀` binders instead of `λ` binders. `mkLetFVars`
  creates `let` binders.
- `mkArrow` is the non-dependent version of `mkForallFVars` which construcs
  a function type `X → Y`. Since the type is non-dependent, there is no need
  for temporary `fvar`s.

Using all these functions, we can construct larger expressions such as this one:

```lean
λ (f : Nat → Nat), ∀ (n : Nat), f n = f (n + 1)
```
-/

def somePropExpr : MetaM Expr := do
  let funcType ← mkArrow (.const ``Nat []) (.const ``Nat [])
  withLocalDecl `f BinderInfo.default funcType fun f => do
    let feqn ← withLocalDecl `n BinderInfo.default (.const ``Nat []) fun n => do
      let lhs := .app f n
      let rhs := .app f (← mkAppM ``Nat.succ #[n])
      let eqn ← mkEq lhs rhs
      mkForallFVars #[n] eqn
    mkLambdaFVars #[f] feqn

/-!
The next line registers `someProp` as a name for the expression we've just
constructed, allowing us to play with it more easily. The mechanisms behind this
are discussed in the Elaboration chapter.
-/

elab "someProp" : term => somePropExpr

#check someProp
-- fun f => ∀ (n : Nat), f n = f (Nat.succ n) : (Nat → Nat) → Prop
#reduce someProp Nat.succ
-- ∀ (n : Nat), Nat.succ n = Nat.succ (Nat.succ n)


/-!
### Deconstructing Expressions

Just like we can construct expressions more easily in `MetaM`, we can also
deconstruct them more easily. Particularly useful is a family of functions for
deconstructing expressions which start with `λ` and `∀` binders.

When we are given a type of the form `∀ (x₁ : T₁) ... (xₙ : Tₙ), U`, we are
often interested in doing something with the conclusion `U`. For instance, the
`apply` tactic, when given an expression `e : ∀ ..., U`, compares `U` with the
current target to determine whether `e` can be applied.

To do this, we could repeatedly match on the type expression, removing `∀`
binders until we get to `U`. But this would leave us with an `U` containing
unbound `bvar`s, which, as we saw, is bad. Instead, we use
`Lean.Meta.forallTelescope` of type

```
forallTelescope (type : Expr) (k : Array Expr → Expr → MetaM α) : MetaM α
```

Given `type = ∀ (x₁ : T₁) ... (xₙ : Tₙ), U x₁ ... xₙ`, this function creates one
fvar `fᵢ` for each `∀`-bound variable `xᵢ` and replaces each `xᵢ` with `fᵢ` in
the conclusion `U`. It then calls the computation `k`, passing it the `fᵢ` and
the conclusion `U f₁ ... fₙ`. Within this computation, the `fᵢ` are registered
in the local context; afterwards, they are deleted again (similar to
`withLocalDecl`).

There are many useful variants of `forallTelescope`:

- `forallTelescopeReducing`: like `forallTelescope` but matching is performed up
  to computation. This means that if you have an expression `X` which is
  different from but defeq to `∀ x, P x`, `forallTelescopeReducing X` will
  deconstruct `X` into `x` and `P x`. The non-reducing `forallTelescope` would
  not recognise `X` as a quantified expression. The matching is performed by
  essentially calling `whnf` repeatedly, using the ambient transparency.
- `forallBoundedTelescope`: like `forallTelescopeReducing` (even though there is
  no "reducing" in the name) but stops after a specified number of `∀` binders.
- `forallMetaTelescope`, `forallMetaTelescopeReducing`,
  `forallMetaBoundedTelescope`: like the corresponding non-`meta` functions, but
  the bound variables are replaced by new `mvar`s instead of `fvar`s. Unlike the
  non-`meta` functions, the `meta` functions do not delete the new metavariables
  after performing some computation, so the metavariables remain in the
  environment indefinitely.
- `lambdaTelescope`, `lambdaTelescopeReducing`, `lambdaBoundedTelescope`,
  `lambdaMetaTelescope`: like the corresponding `forall` functions, but for
  `λ` binders instead of `∀`.

Using one of the telescope functions, we can implement our own `apply` tactic:
-/

def myApply (goal : MVarId) (e : Expr) : MetaM (List MVarId) := do
  -- Check that the goal is not yet assigned.
  goal.checkNotAssigned `myApply
  -- Operate in the local context of the goal.
  goal.withContext do
    -- Get the goal's target type.
    let target ← goal.getType
    -- Get the type of the given expression.
    let type ← inferType e
    -- If `type` has the form `∀ (x₁ : T₁) ... (xₙ : Tₙ), U`, introduce new
    -- metavariables for the `xᵢ` and obtain the conclusion `U`. (If `type` does
    -- not have this form, `args` is empty and `conclusion = type`.)
    let (args, _, conclusion) ← forallMetaTelescopeReducing type
    -- If the conclusion unifies with the target:
    if ← isDefEq target conclusion then
      -- Assign the goal to `e x₁ ... xₙ`, where the `xᵢ` are the fresh
      -- metavariables in `args`.
      goal.assign (mkAppN e args)
      -- `isDefEq` may have assigned some of the `args`. Report the rest as new
      -- goals.
      let newGoals ← args.filterMapM λ mvar => do
        let mvarId := mvar.mvarId!
        if ! (← mvarId.isAssigned) && ! (← mvarId.isDelayedAssigned) then
          return some mvarId
        else
          return none
      return newGoals.toList
    -- If the conclusion does not unify with the target, throw an error.
    else
      throwTacticEx `myApply goal m!"{e} is not applicable to goal with target {target}"

/-!
The real `apply` does some additional pre- and postprocessing, but the core
logic is what we show here. To test our tactic, we need an elaboration
incantation, more about which in the Elaboration chapter.
-/

elab "myApply" e:term : tactic => do
  let e ← Elab.Term.elabTerm e none
  Elab.Tactic.liftMetaTactic (myApply · e)

example (h : α → β) (a : α) : β := by
  myApply h
  myApply a


/-!
## Backtracking

Many tactics naturally require backtracking: the ability to go back to a
previous state, as if the tactic had never been executed. A few examples:

- `first | t | u` first executes `t`. If `t` fails, it backtracks and executes
  `u`.
- `try t` executes `t`. If `t` fails, it backtracks to the initial state,
  erasing any changes made by `t`.
- `trivial` attempts to solve the goal using a number of simple tactics
  (e.g. `rfl` or `contradiction`). After each unsuccessful application of such a
  tactic, `trivial` backtracks.

Good thing, then, that Lean's core data structures are designed to enable easy
and efficient backtracking. The corresponding API is provided by the
`Lean.MonadBacktrack` class. `MetaM`, `TermElabM` and `TacticM` are all
instances of this class. (`CoreM` is not but could be.)

`MonadBacktrack` provides two fundamental operations:

- `Lean.saveState : m s` returns a representation of the current state, where
  `m` is the monad we are in and `s` is the state type. E.g. for `MetaM`,
  `saveState` returns a `Lean.Meta.SavedState` containing the current
  environment, the current `MetavarContext` and various other pieces of
  information.
- `Lean.restoreState : s → m Unit` takes a previously saved state and restores
  it. This effectively resets the compiler state to the previous point.

With this, we can roll our own `MetaM` version of the `try` tactic:
-/

def tryM (x : MetaM Unit) : MetaM Unit := do
  let s ← saveState
  try
    x
  catch _ =>
    restoreState s

/-!
We first save the state, then execute `x`. If `x` fails, we backtrack the state.

The standard library defines many combinators like `tryM`. Here are the most
useful ones:

- `Lean.withoutModifyingState (x : m α) : m α` executes the action `x`, then
  resets the state and returns `x`'s result. You can use this, for example, to
  check for definitional equality without assigning metavariables:
  ```lean
  withoutModifyingState $ isDefEq x y
  ```
  If `isDefEq` succeeds, it may assign metavariables in `x` and `y`. Using
  `withoutModifyingState`, we can make sure this does not happen.
- `Lean.observing? (x : m α) : m (Option α)` executes the action `x`. If `x`
  succeeds, `observing?` returns its result. If `x` fails (throws an exception),
  `observing?` backtracks the state and returns `none`. This is a more
  informative version of our `tryM` combinator.
- `Lean.commitIfNoEx (x : α) : m α` executes `x`. If `x` succeeds,
  `commitIfNoEx` returns its result. If `x` throws an exception, `commitIfNoEx`
  backtracks the state and rethrows the exception.

Note that the builtin `try ... catch ... finally` does not perform any
backtracking. So code which looks like this is probably wrong:

```lean
try
  doSomething
catch e =>
  doSomethingElse
```

The `catch` branch, `doSomethingElse`, is executed in a state containing
whatever modifications `doSomething` made before it failed. Since we probably
want to erase these modifications, we should write instead:

```lean
try
  commitIfNoEx doSomething
catch e =>
  doSomethingElse
```

Another `MonadBacktrack` gotcha is that `restoreState` does not backtrack the
*entire* state. Caches, trace messages and the global name generator, among
other things, are not backtracked, so changes made to these parts of the state
are not reset by `restoreState`. This is usually what we want: if a tactic
executed by `observing?` produces some trace messages, we want to see them even
if the tactic fails. See `Lean.Meta.SavedState.restore` and `Lean.Core.restore`
for details on what is and is not backtracked.

In the next chapter, we move towards the topic of elaboration, of which
you've already seen several glimpses in this chapter. We start by discussing
Lean's syntax system, which allows you to add custom syntactic constructs to the
Lean parser.

## 习题

1. [**元变量**] 创建一个类型为 `Nat` 的元变量，并为其赋值 `3`。
请注意，更改元变量的类型，例如从 `Nat` 更改为 `String` 不会引发任何错误 - 这就是为什么我们必须确保 **「(a) `val` 必须具有 `mvarId` 的目标类型，并且 (b) `val` 必须仅包含来自 `mvarId` 局部语境的 `fvars`」**。
2. [**元变量**] `instantiateMVars (Lean.mkAppN (Expr.const 'Nat.add []) #[mkNatLit 1, mkNatLit 2])` 会输出什么？
3. [**元变量**] 填写以下代码中缺失的行。

    ```lean
    #eval show MetaM Unit from do
      let oneExpr := Expr.app (Expr.const `Nat.succ []) (Expr.const ``Nat.zero [])
      let twoExpr := Expr.app (Expr.const `Nat.succ []) oneExpr

      -- 创建 `mvar1` 类型为 `Nat`
      -- let mvar1 ← ...
      -- 创建 `mvar2` 类型为 `Nat`
      -- let mvar2 ← ...
      -- 创建 `mvar3` 类型为 `Nat`
      -- let mvar3 ← ...

      -- 指派 `mvar1` 为 `2 + ?mvar2 + ?mvar3`
      -- ...

      -- 指派 `mvar3` 为 `1`
      -- ...

      -- 实例化 `mvar1`，结果为表达式 `2 + ?mvar2 + 1`
      ...
    ```
4. [**元变量**] 考虑下面的定理 `red`和策略 `explore`。
  **a)** 元变量 `mvarId` 的 `type` 和 `userName` 是什么？
  **b)** 这个元变量的局部语境中所有的局部声明的 `type` 和 `userName` 是什么？
  打印所有这些东西。

    ```lean
    elab "explore" : tactic => do
      let mvarId : MVarId ← Lean.Elab.Tactic.getMainGoal
      let metavarDecl : MetavarDecl ← mvarId.getDecl

      IO.println "Our metavariable"
      -- ...

      IO.println "All of its local declarations"
      -- ...

    theorem red (hA : 1 = 1) (hB : 2 = 2) : 2 = 2 := by
      explore
      sorry
    ```
5. [**元变量**] 写一个策略 `solve` 来证明定理 `red`。
6. [**计算**] 写出下面表达式的一般形式：
  **a)** `fun x => x` 类型为 `Bool → Bool`
  **b)** `(fun x => x) ((true && false) || true)` 类型为 `Bool`
  **c)** `800 + 2` 类型为 `Nat`
7. [**计算**] 说明 `Expr.lit (Lean.Literal.natVal 1)` 和 `Expr.app (Expr.const ``Nat.succ []) (Expr.const ``Nat.zero [])` 创建的 `1` 是定义等价的。
8. [**计算**] 确定下面的表达式是否是定义等价的。如果 `Lean.Meta.isDefEq` 成功了，且它给元变量赋值，写出赋值。
  **a)** `5 =?= (fun x => 5) ((fun y : Nat → Nat => y) (fun z : Nat => z))`
  **b)** `2 + 1 =?= 1 + 2`
  **c)** `?a =?= 2`，其中 `?a` 具有类型 `String`
  **d)** `?a + Int =?= "hi" + ?b`，其中 `?a` 和 `?b` 没有类型。
  **e)** `2 + ?a =?= 3`
  **f)** `2 + ?a =?= 2 + 1`
9. [**计算**] 你预计下面的代码会有怎么样的输出？

    ```lean
    @[reducible] def reducibleDef     : Nat := 1 -- same as `abbrev`
    @[instance] def instanceDef       : Nat := 2 -- same as `instance`
    def defaultDef                    : Nat := 3
    @[irreducible] def irreducibleDef : Nat := 4

    @[reducible] def sum := [reducibleDef, instanceDef, defaultDef, irreducibleDef]

    #eval show MetaM Unit from do
      let constantExpr := Expr.const `sum []

      Meta.withTransparency Meta.TransparencyMode.reducible do
        let reducedExpr ← Meta.reduce constantExpr
        dbg_trace (← ppExpr reducedExpr) -- ...

      Meta.withTransparency Meta.TransparencyMode.instances do
        let reducedExpr ← Meta.reduce constantExpr
        dbg_trace (← ppExpr reducedExpr) -- ...

      Meta.withTransparency Meta.TransparencyMode.default do
        let reducedExpr ← Meta.reduce constantExpr
        dbg_trace (← ppExpr reducedExpr) -- ...

      Meta.withTransparency Meta.TransparencyMode.all do
        let reducedExpr ← Meta.reduce constantExpr
        dbg_trace (← ppExpr reducedExpr) -- ...

      let reducedExpr ← Meta.reduce constantExpr
      dbg_trace (← ppExpr reducedExpr) -- ...
    ```
10. [**构建表达式**] 通过两种方式创建表达式 `fun x, 1 + x`：
  **a)** not idiomatically, with loose bound variables
  **b)** idiomatically.
  你可以在哪种方式中使用 `Lean.mkAppN`? 还有 `Lean.Meta.mkAppM`?
11. [**构建表达式**] 创建表达式 `∀ (yellow: Nat), yellow`。
12. [**构建表达式**] 通过两种方式创建表达式 `∀ (n : Nat), n = n + 1`：
  **a)** not idiomatically, with loose bound variables
  **b)** idiomatically.
  In what version can you use `Lean.mkApp3`? In what version can you use `Lean.Meta.mkEq`?
13. [**构建表达式**] 创建表达式 `fun (f : Nat → Nat), ∀ (n : Nat), f n = f (n + 1)` idiomatically.
14. [**构建表达式**] 你预计下面的代码会有怎么样的输出？

    ```lean
    #eval show Lean.Elab.Term.TermElabM _ from do
      let stx : Syntax ← `(∀ (a : Prop) (b : Prop), a ∨ b → b → a ∧ a)
      let expr ← Elab.Term.elabTermAndSynthesize stx none

      let (_, _, conclusion) ← forallMetaTelescope expr
      dbg_trace conclusion -- ...

      let (_, _, conclusion) ← forallMetaBoundedTelescope expr 2
      dbg_trace conclusion -- ...

      let (_, _, conclusion) ← lambdaMetaTelescope expr
      dbg_trace conclusion -- ...
    ```
15. [**回溯**] 使用 `isDefEq` 检查表达式 `?a + Int` 和 `"hi" + ?b` 是否定义等价（确保为你的元变量使用正确的类型或 `Option.none`）。使用 `saveState` 和 `restoreState` 来恢复元变量赋值。
-/
