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

元变量深度也是一个较为小众的特性，但有时会派上用场。每个元变量都有一个**深度**（一个自然数），并且 `MetavarContext` 也有一个相应的深度。Lean 只有在元变量的深度等于当前 `MetavarContext` 的深度时才会为其赋值。新创建的元变量继承 `MetavarContext` 的深度，因此默认情况下，每个元变量都是可赋值的。

这种机制在某些策略需要一些临时元变量，并且需要确保其他非临时元变量不会被赋值时会很有用。为了实现这一点，策略可以按照以下步骤进行：

1. 保存当前的 `MetavarContext`。
2. 增加 `MetavarContext` 的深度。
3. 执行必要的计算，可能会创建和赋值元变量。新创建的元变量位于当前 `MetavarContext` 的深度，因此可以被赋值。而旧的元变量位于较低的深度，因此不能被赋值。
4. 恢复保存的 `MetavarContext`，从而清除所有临时元变量并重置 `MetavarContext` 的深度。

这种模式封装在 `Lean.Meta.withNewMCtxDepth` 中。

## 计算

计算是依值类型理论的核心概念。项 `2`、`Nat.succ 1` 和 `1 + 1` 在计算出相同值的意义上是等价的。我们称它们为**定义等价**。从元编程的角度来看，问题在于定义等价的项可能由完全不同的表达式表示，但我们的用户通常期望适用于 `2` 的策略也适用于 `1 + 1`。因此，当我们编写策略时，必须做额外的工作，以确保定义等价的项得到类似的处理。

### 完全标准化

我们能对计算做的最简单的事情就是将项标准化。对于某些数字类型的例外情况，类型为 `T` 的项 `t` 的标准式是 `T` 构造函数的应用序列。例如，列表的标准式是 `List.cons` 和 `List.nil` 的应用序列。

将项标准化（即将其带入标准式）的函数是 `Lean.Meta.reduce`，其类型签名为：

```lean
reduce (e : Expr) (explicitOnly skipTypes skipProofs := true) : MetaM Expr
```

我们可以这样使用它：
-/

def someNumber : Nat := (· + 2) $ 3

#eval Expr.const ``someNumber []
-- Lean.Expr.const `someNumber []

#eval reduce (Expr.const ``someNumber [])
-- Lean.Expr.lit (Lean.Literal.natVal 5)

/-!
顺便说一下，这表明类型为 `Nat` 的项的标准式并不总是 `Nat` 构造函数的应用，它也可以是一个字面量。此外，注意 `#eval` 不仅可以用于计算项，还可以用于执行 `MetaM` 程序。

`reduce` 的可选填参数允许我们跳过表达式的某些部分。例如，`reduce e (explicitOnly := true)` 不会标准化表达式 `e` 中的任何隐式参数。这可以带来更好的性能：由于标准式可能非常庞大，跳过用户无须看到的表达式部分可能是个好主意。

`#reduce` 命令本质上就是 `reduce` 的一个应用：
-/

#reduce someNumber
-- 5

/-!
### 透明度

Lean 4 元编程中的一个复杂但重要的细节是，任何给定的表达式都不只有一个标准式，而是根据给定的**透明度（transparency）**来确定其标准式。

透明度是 `Lean.Meta.TransparencyMode` 的一个枚举值，具有四个选项：`reducible`、`instances`、`default` 和 `all`。任何 `MetaM` 计算都可以访问一个环境透明度模式，使用 `Lean.Meta.getTransparency` 获取。

当前的透明度决定了在标准化过程中（如通过 `reduce`）哪些常量会被展开。（展开常量是指用其定义替换常量本身。）这四个设置逐步展开更多的常量：

- `reducible`：只展开带有 `@[reducible]` 属性的常量。注意，`abbrev` 是 `@[reducible] def` 的简写。
- `instances`：展开可归约 `reducible` 常量以及带有 `@[instance]` 属性的常量。同样，`instance` 命令是 `@[instance] def` 的简写。
- `default`：展开所有常量，除了那些被标记为 `@[irreducible]` 的常量。
- `all`：展开所有常量，即使是那些被标记为 `@[irreducible]` 的常量。

环境透明度通常为 `default`。要以特定透明度执行操作，使用 `Lean.Meta.withTransparency`。也有一些特定透明度的简写，例如 `Lean.Meta.withReducible`。

将所有内容结合在一起看一个示例（我们使用 `Lean.Meta.ppExpr` 来美观打印表达式）：
-/

def traceConstWithTransparency (md : TransparencyMode) (c : Name) :
    MetaM Format := do
  ppExpr (← withTransparency md $ reduce (.const c []))

@[irreducible] def irreducibleDef : Nat      := 1
def                defaultDef     : Nat      := irreducibleDef + 1
abbrev             reducibleDef   : Nat      := defaultDef + 1

/-!
我们从 `reducible` 透明度开始，它只展开 `reducibleDef`:
-/

#eval traceConstWithTransparency .reducible ``reducibleDef
-- defaultDef + 1

/-!
如果我们重复上述命令，并让 Lean 打印出隐式参数，我们可以看到 `+` 符号实际上是 `hAdd` 函数的应用，而该函数是 `HAdd` 类型类的一个成员：
-/

set_option pp.explicit true in
#eval traceConstWithTransparency .reducible ``reducibleDef
-- @HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) defaultDef 1

/-!
当我们使用 `instances` 透明度进行归约时，这个应用被展开并替换为 `Nat.add`：
-/

#eval traceConstWithTransparency .instances ``reducibleDef
-- Nat.add defaultDef 1

/-!
使用 `default` 透明度时，`Nat.add` 也会被展开：
-/

#eval traceConstWithTransparency .default ``reducibleDef
-- Nat.succ (Nat.succ irreducibleDef)

/-!
使用 `TransparencyMode.all` 时，我们最终能够展开 `irreducibleDef`：
-/

#eval traceConstWithTransparency .all ``reducibleDef
-- 3

/-!
`#eval` 命令展示了同一个术语 `reducibleDef` 可以在每种透明度下具有不同的标准式。

为什么要有这么多步骤？基本上是为了性能：如果我们允许标准化总是展开每个常量，诸如类型类搜索等操作的开销将变得无法接受。权衡在于我们必须为每个涉及标准化的操作选择适当的透明度。

### 弱头标准化（Weak Head Normalisation）

透明度解决了标准化中的一些性能问题。但更重要的是要认识到，对于许多情况，我们根本不需要完全标准化术语。假设我们正在构建一个自动拆分类型为 `P ∧ Q` 的假设的策略。如果 `X` 归约为 `P ∧ Q`，我们可能希望这个策略能够识别出假设 `h : X`。但是，如果 `P` 进一步归约为 `Y ∨ Z`，具体的 `Y` 和 `Z` 对我们来说并不重要，归约 `P` 就成了多余的工作。

这种情况非常常见，因此完全标准化的 `reduce` 实际上很少使用。Lean 中标准化的主力工具是 `whnf`，它将表达式简化为**弱头标准式**（WHNF）。

简单来说，当表达式 `e` 具有如下形式时，它处于弱头标准式：

```text
e = f x₁ ... xₙ   (n ≥ 0)
```

并且 `f` 在当前透明度下不能被进一步归约。为了方便检查表达式的 WHNF，我们定义了一个函数 `whnf'`，使用了一些将在繁饰章节中讨论的函数。
-/

open Lean.Elab.Term in
def whnf' (e : TermElabM Syntax) : TermElabM Format := do
  let e ← elabTermAndSynthesize (← e) none
  ppExpr (← whnf e)

/-!
以下是一些 WHNF（弱头归一形式）中的表达式示例。

构造子的应用处于 WHNF（某些数字类型除外）：
-/

#eval whnf' `(List.cons 1 [])
-- [1]

/-!
WHNF 中应用的**参数**本身可能是 WHNF，也可能不是：
-/

#eval whnf' `(List.cons (1 + 1) [])
-- [1 + 1]

/-!
如果当前透明度不允许我们展开常量，那么常量的应用处于 WHNF：
-/

#eval withTransparency .reducible $ whnf' `(List.append [1] [2])
-- List.append [1] [2]

/-!
Lambda 表达式处于 WHNF：
-/

#eval whnf' `(λ x : Nat => x)
-- fun x => x

/-!
全称量词（Foralls）处于 WHNF：
-/

#eval whnf' `(∀ x, x > 0)
-- ∀ (x : Nat), x > 0

/-!
类型处于 WHNF：
-/

#eval whnf' `(Type 3)
-- Type 3

/-!
字面量处于 WHNF：
-/

#eval whnf' `((15 : Nat))
-- 15

/-!
以下是一些处于 WHNF（弱头归一形式）的表达式，这些表达式测试起来有些棘手：

```lean
?x 0 1  -- 假设元变量 `?x` 未被赋值，它处于 WHNF。
h 0 1   -- 假设 `h` 是一个局部假设，它处于 WHNF。
```

另一方面，以下是不处于 WHNF 的一些表达式。

如果当前透明度允许我们展开常量，那么常量的应用不处于 WHNF：
-/

#eval whnf' `(List.append [1])
-- fun x => 1 :: List.append [] x

/-!
Lambda 表达式的应用不处于 WHNF：
-/

#eval whnf' `((λ x y : Nat => x + y) 1)
-- `fun y => 1 + y`

/-!
`let` 绑定不处于 WHNF：
-/

#eval whnf' `(let x : Nat := 1; x)
-- 1

/-!
再次来看一些棘手的例子：

```lean
?x 0 1 -- 假设 `?x` 被赋值（例如赋值为 `Nat.add`），它的应用不处于 WHNF。
h 0 1  -- 假设 `h` 是一个局部定义（例如值为 `Nat.add`），它的应用不处于 WHNF。
```

回到本节的动机策略，让我们编写一个函数，用于匹配类型形式为 `P ∧ Q`，同时避免额外的计算。WHNF 使得这一操作变得简单：
-/

def matchAndReducing (e : Expr) : MetaM (Option (Expr × Expr)) := do
  match ← whnf e with
  | (.app (.app (.const ``And _) P) Q) => return some (P, Q)
  | _ => return none

/-
通过使用 `whnf`，我们确保如果 `e` 计算为 `P ∧ Q` 形式的内容，我们能够检测到。但与此同时，我们不会在 `P` 或 `Q` 中执行任何不必要的计算。

然而，我们的「避免不必要的计算」原则也意味着，如果我们想在表达式上进行更深层次的匹配，需要多次使用 `whnf`。假设我们想匹配 `P ∧ Q ∧ R` 形式的类型，正确的做法是使用 `whnf` 两次：
-/

def matchAndReducing₂ (e : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  match ← whnf e with
  | (.app (.app (.const ``And _) P) e') =>
    match ← whnf e' with
    | (.app (.app (.const ``And _) Q) R) => return some (P, Q, R)
    | _ => return none
  | _ => return none

/-!
这种基于计算的深层匹配是可以自动化的。但在有人构建这种自动化工具之前，我们必须自己确定所需的 `whnf` 调用。

### 定义等价

如前述，定义等价是基于计算的相等性。如果两个表达式 `t` 和 `s` 的标准式相等（在当前透明度下），它们就是定义等价（简写作defeq）的。

要检查两个表达式是否定义等价，可以使用 `Lean.Meta.isDefEq`，其类型签名为：

```lean
isDefEq : Expr → Expr → MetaM Bool
```

尽管定义等价是通过标准式定义的，但 `isDefEq` 实际上并不会计算参数的标准式，因为这代价太高。相反，它尝试以尽可能少的归约来「匹配」 `t` 和 `s`。这是一项启发式的任务，当启发式方法失效时，`isDefEq` 的计算代价可能非常高。在最坏的情况下，它可能不得不频繁地归约 `s` 和 `t`，最终它们仍会以标准式结束。不过，通常情况下，启发式方法是有效的，`isDefEq` 速度相对较快。

如果表达式 `t` 和 `u` 包含可赋值的元变量，`isDefEq` 可能会将这些元变量赋值，使得 `t` 与 `u` 定义等价。我们也可以说 `isDefEq` **合一（unify）** 了 `t` 和 `u`；这种合一查询有时写作 `t =?= u`。例如，合一 `List ?m =?= List Nat` 成功并赋值 `?m := Nat`。合一 `Nat.succ ?m =?= n + 1` 成功并赋值 `?m := n`。合一 `?m₁ + ?m₂ + ?m₃ =?= m + n - k` 失败，且没有元变量被赋值（尽管表达式之间存在「部分匹配」）。

`isDefEq` 是否将一个元变量视为可赋值由两个因素决定：

1. 元变量的深度必须等于当前 `MetavarContext` 的深度。参见[元变量深度部分](#元变量深度)。
2. 每个元变量都有一个**种类**（kind）（`MetavarKind` 类型的值），其唯一目的是修改 `isDefEq` 的行为。可能的种类包括：
   - 自然：`isDefEq` 可以自由地赋值该元变量。这是默认值。
   - 合成：`isDefEq` 可以赋值该元变量，但如果可能，尽量避免赋值。例如，假设 `?n` 是一个自然元变量，而 `?s` 是一个合成元变量。当面对 `?s =?= ?n` 的合一问题时，`isDefEq` 会赋值 `?n` 而不是 `?s`。
   - 合成不透明：`isDefEq` 永远不会赋值该元变量。

## 构造表达式

在前一章中，我们看到了用于构建表达式的一些基本函数：`Expr.app`、`Expr.const`、`mkAppN` 等。这些函数本身没有问题，但 `MetaM` 的附加功能通常提供了更方便的方式。

### 应用

当我们编写常规的 Lean 代码时，Lean 会帮助我们推断许多隐式参数和宇宙级别。如果不这样做，我们的代码将显得相当冗长：
-/

def appendAppend (xs ys : List α) := (xs.append ys).append xs

set_option pp.all true in
set_option pp.explicit true in
#print appendAppend
-- def appendAppend.{u_1} : {α : Type u_1} → List.{u_1} α → List.{u_1} α → List.{u_1} α :=
-- fun {α : Type u_1} (xs ys : List.{u_1} α) => @List.append.{u_1} α (@List.append.{u_1} α xs ys) xs

/-!
`.{u_1}` 后缀是宇宙级别，必须为每个多态常量提供。当然，类型 `α` 也会被传递到各处。

在元编程中构造表达式时也会遇到完全相同的问题。一个手工构建的表达式，表示上述定义的右侧，看起来是这样的：
-/

def appendAppendRHSExpr₁ (u : Level) (α xs ys : Expr) : Expr :=
  mkAppN (.const ``List.append [u])
    #[α, mkAppN (.const ``List.append [u]) #[α, xs, ys], xs]

/-!
必须指定隐式参数和宇宙级别是很麻烦且容易出错的。因此，`MetaM` 提供了一个帮助函数，允许我们省略隐式信息：`Lean.Meta.mkAppM`，其类型为：

```lean
mkAppM : Name → Array Expr → MetaM Expr
```

与 `mkAppN` 类似，`mkAppM` 构造一个应用。但是，`mkAppN` 需要我们自己提供所有的宇宙级别和隐式参数，而 `mkAppM` 会自动推断它们。这意味着我们只需要提供显式参数，示例因此也会简短得多：
-/

def appendAppendRHSExpr₂ (xs ys : Expr) : MetaM Expr := do
  mkAppM ``List.append #[← mkAppM ``List.append #[xs, ys], xs]

/-!
注意，这里没有出现任何 `α` 和 `u`。`mkAppM` 还有一个变体 `mkAppM'`，它将第一个参数从 `Name` 改为 `Expr`，允许我们构造非常量表达式的应用。

不过，`mkAppM` 并不是万能的：如果你写 `mkAppM ``List.append #[]`，在运行时会报错。这是因为 `mkAppM` 尝试确定类型 `α`，但由于 `append` 没有给出任何参数，`α` 可以是任何类型，因此 `mkAppM` 无法成功推断。

另一个有时很有用的 `mkAppM` 变体是 `Lean.Meta.mkAppOptM`，其类型为：

```lean
mkAppOptM : Name → Array (Option Expr) → MetaM Expr
```

与 `mkAppM` 总是推断隐式和实例参数并且要求我们提供显式参数不同，`mkAppOptM` 让我们可以自由选择提供哪些参数以及推断哪些参数。例如，我们可以显式地提供实例，在下面的示例中，我们用它来提供一个非标准的 `Ord` 实例。
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
与 `mkAppM` 类似，`mkAppOptM` 也有一个加了撇号的变体 `Lean.Meta.mkAppOptM'`，它将第一个参数从 `Name` 改为 `Expr`。包含 `mkAppM` 的文件还包含了其他各种帮助函数，例如用于构造列表字面量或 `sorry` 的函数。

### Lambdas 和 Foralls

另一个常见的任务是构造涉及 `λ` 或 `∀` 绑定的表达式。假设我们想创建表达式 `λ (x : Nat), Nat.add x x`。一种方法是直接写出 lambda：
-/

def doubleExpr₁ : Expr :=
  .lam `x (.const ``Nat []) (mkAppN (.const ``Nat.add []) #[.bvar 0, .bvar 0])
    BinderInfo.default

#eval ppExpr doubleExpr₁
-- fun x => Nat.add x x

/-!
这种方法虽然有效，但直接使用 `bvar` 是非常不符合惯例的。Lean 使用所谓的**局部封闭（locally closed）**变量表示法。这意味着 Lean API 中除了最低层的函数外，其他函数都期望表达式不包含「松弛的 `bvar`」，其中松弛的意思是，如果它没有被同一个表达式中的某个绑定器绑定。（在 Lean 之外，这样的变量通常被称为「自由变量」。名称 `bvar` —— "bound variable"（绑定变量） —— 已经表明 `bvar` 永远不应是自由的。）

因此，如果在上面的例子中，我们用稍微高层的 `mkAppM` 替换 `mkAppN`，会导致运行时错误。按照局部封闭的约定，`mkAppM` 期望任何传递给它的表达式都不包含松弛的绑定变量，而 `.bvar 0` 恰好就是这样的松弛变量。

因此，Lean 的做法是通过两步构造带有绑定变量的表达式，而不是直接使用 `bvar`：

1. 构造表达式的主体（在我们的例子中是 lambda 的主体），使用临时的局部假设（`fvar`）来代替绑定变量。
2. 将这些 `fvar` 替换为 `bvar`，同时添加相应的 lambda 绑定器。

这个过程确保我们不需要在任何时候处理带有松弛 `bvar` 的表达式（除了步骤 2，它是通过专门的函数「原子化」执行的）。将该过程应用于我们的例子：
-/

def doubleExpr₂ : MetaM Expr :=
  withLocalDecl `x BinderInfo.default (.const ``Nat []) λ x => do
    let body ← mkAppM ``Nat.add #[x, x]
    mkLambdaFVars #[x] body

#eval show MetaM _ from do
  ppExpr (← doubleExpr₂)
-- fun x => Nat.add x x

/-!
这里有两个新函数。首先，`Lean.Meta.withLocalDecl` 的类型为：

```lean
withLocalDecl (name : Name) (bi : BinderInfo) (type : Expr) (k : Expr → MetaM α) : MetaM α
```

给定一个变量名称、绑定器信息和类型，`withLocalDecl` 构造一个新的 `fvar` 并将其传递给计算 `k`。在执行 `k` 时，该 `fvar` 在局部上下文中可用，但在之后会被删除。

第二个新函数是 `Lean.Meta.mkLambdaFVars`，其类型（忽略一些可选填参数）为：

```lean
mkLambdaFVars : Array Expr → Expr → MetaM Expr
```

此函数接受一个 `fvar` 数组和一个表达式 `e`。然后为每个 `fvar` `x` 添加一个 lambda 绑定器，并将 `e` 中的每个 `x` 替换为与新 lambda 绑定器对应的绑定变量。返回的表达式不再包含 `fvar`，这是很好的，因为当我们离开 `withLocalDecl` 上下文时，`fvar` 就会消失。（尽管名称中有 `fvar`，但我们也可以将 `mvar` 传递给 `mkLambdaFVars`。）

以下是这些函数的有用变体：

- `withLocalDecls` 声明多个临时 `fvar`。
- `mkForallFVars` 创建 `∀` 绑定器而不是 `λ` 绑定器。`mkLetFVars` 创建 `let` 绑定器。
- `mkArrow` 是 `mkForallFVars` 的非依赖版本，它构造函数类型 `X → Y`。由于类型是非依赖的，因此不需要临时 `fvar`。

使用所有这些函数，我们可以构造更大的表达式，例如：

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
下一行将 `someProp` 注册为我们刚刚构造的表达式的名称，使我们可以更轻松地操作它。其背后的机制将在繁饰章节中讨论。
-/

elab "someProp" : term => somePropExpr

#check someProp
-- fun f => ∀ (n : Nat), f n = f (Nat.succ n) : (Nat → Nat) → Prop
#reduce someProp Nat.succ
-- ∀ (n : Nat), Nat.succ n = Nat.succ (Nat.succ n)


/-!
### 解构表达式

就像我们可以在 `MetaM` 中更轻松地构造表达式一样，我们也可以更轻松地解构表达式。特别有用的是一组用于解构以 `λ` 和 `∀` 绑定器开头的表达式的函数。

当我们得到形如 `∀ (x₁ : T₁) ... (xₙ : Tₙ), U` 的类型时，通常我们会对结论 `U` 做一些操作。例如，当给定一个表达式 `e : ∀ ..., U` 时，`apply` 策略会比较 `U` 与当前目标，以确定是否可以应用 `e`。

为此，我们可以重复匹配类型表达式，逐步去除 `∀` 绑定器，直到得到 `U`。但这样会导致 `U` 包含未绑定的 `bvar`，如我们所见，这不是好事。相反，我们使用 `Lean.Meta.forallTelescope`，其类型为：

```lean
forallTelescope (type : Expr) (k : Array Expr → Expr → MetaM α) : MetaM α
```

给定 `type = ∀ (x₁ : T₁) ... (xₙ : Tₙ), U x₁ ... xₙ`，此函数为每个 `∀` 绑定的变量 `xᵢ` 创建一个 `fvar` `fᵢ`，并在结论 `U` 中将每个 `xᵢ` 替换为 `fᵢ`。然后它调用计算 `k`，传递 `fᵢ` 和结论 `U f₁ ... fₙ`。在此计算中，`fᵢ` 会注册在局部语境中；计算结束后，它们会被删除（类似于 `withLocalDecl`）。

`forallTelescope` 有许多有用的变体：

- `forallTelescopeReducing`：与 `forallTelescope` 类似，但匹配是在计算后执行的。这意味着如果你有一个表达式 `X`，它不同于但定义等同于 `∀ x, P x`，`forallTelescopeReducing X` 会将 `X` 解构为 `x` 和 `P x`。非归约的 `forallTelescope` 不会识别 `X` 为量化表达式。匹配是通过重复调用 `whnf` 来执行的，使用环境透明度。
- `forallBoundedTelescope`：类似于 `forallTelescopeReducing`（尽管名称中没有“reducing”），但在指定数量的 `∀` 绑定器之后停止。
- `forallMetaTelescope`，`forallMetaTelescopeReducing`，`forallMetaBoundedTelescope`：与相应的非 `meta` 函数类似，但绑定变量被替换为新的 `mvar` 而不是 `fvar`。与非 `meta` 函数不同，`meta` 函数在执行某些计算后不会删除新的元变量，因此这些元变量将无限期保留在环境中。
- `lambdaTelescope`，`lambdaTelescopeReducing`，`lambdaBoundedTelescope`，`lambdaMetaTelescope`：类似于相应的 `forall` 函数，但用于 `λ` 绑定器，而不是 `∀`。

使用这些 telescope 函数之一，我们可以实现自己的 `apply` 策略：
-/

def myApply (goal : MVarId) (e : Expr) : MetaM (List MVarId) := do
  -- 检查目标是否尚未分配。
  goal.checkNotAssigned `myApply
  -- 在目标的局部上下文中操作。
  goal.withContext do
    -- 获取目标的目标类型。
    let target ← goal.getType
    -- 获取给定表达式的类型。
    let type ← inferType e
    -- 如果 `type` 的形式为 `∀ (x₁ : T₁) ... (xₙ : Tₙ), U`，为 `xᵢ` 引入新的元变量，并获取结论 `U`。
    -- （如果 `type` 没有这种形式，`args` 为空，`conclusion = type`。）
    let (args, _, conclusion) ← forallMetaTelescopeReducing type
    -- 如果结论与目标统一：
    if ← isDefEq target conclusion then
      -- 将目标赋值为 `e x₁ ... xₙ`，其中 `xᵢ` 是 `args` 中的新元变量。
      goal.assign (mkAppN e args)
      -- `isDefEq` 可能已经为 `args` 中的某些变量赋值。报告剩下的作为新的目标。
      let newGoals ← args.filterMapM λ mvar => do
        let mvarId := mvar.mvarId!
        if ! (← mvarId.isAssigned) && ! (← mvarId.isDelayedAssigned) then
          return some mvarId
        else
          return none
      return newGoals.toList
    -- 如果结论与目标不统一，则抛出错误。
    else
      throwTacticEx `myApply goal m!"{e} 无法应用于目标，目标类型为 {target}"

/-!
真正的 `apply` 进行了一些额外的前处理和后处理，但核心逻辑就是我们在这里展示的内容。要测试我们的策略，我们需要一点繁饰的相关内容，等到繁饰章节中讨论。
-/

elab "myApply" e:term : tactic => do
  let e ← Elab.Term.elabTerm e none
  Elab.Tactic.liftMetaTactic (myApply · e)

example (h : α → β) (a : α) : β := by
  myApply h
  myApply a


/-!
## 回溯

许多策略自然需要回溯的能力：也就是能够回到先前的状态，就像策略从未执行过一样。以下是一些例子：

- `first | t | u` 首先执行 `t`，如果 `t` 失败，则回溯并执行 `u`。
- `try t` 执行 `t`，如果 `t` 失败，则回溯到初始状态，撤销 `t` 所做的任何更改。
- `trivial` 试图使用一些简单的策略（例如 `rfl` 或 `contradiction`）解决目标。每次应用这些策略失败后，`trivial` 都会回溯。

幸运的是，Lean 的核心数据结构设计使得回溯变得轻松且高效。相应的 API 由 `Lean.MonadBacktrack` 类提供。`MetaM`、`TermElabM` 和 `TacticM` 都是此类的实例。（`CoreM` 不是，但可以是。）

`MonadBacktrack` 提供了两个基本操作：

- `Lean.saveState : m s` 返回当前状态的表示，其中 `m` 是我们所在的 monad，`s` 是状态类型。例如，对于 `MetaM`，`saveState` 返回一个包含当前环境、当前 `MetavarContext` 以及其他各种信息的 `Lean.Meta.SavedState`。
- `Lean.restoreState : s → m Unit` 接受先前保存的状态并恢复它。这实际上将编译器状态重置为之前的某个点。

通过这些操作，我们可以编写自己的 `MetaM` 版本的 `try` 策略：
-/

def tryM (x : MetaM Unit) : MetaM Unit := do
  let s ← saveState
  try
    x
  catch _ =>
    restoreState s

/-!
我们首先保存状态，然后执行 `x`。如果 `x` 失败，我们会回溯状态。

标准库定义了许多类似 `tryM` 的组合器，以下是最有用的一些：

- `Lean.withoutModifyingState (x : m α) : m α` 执行动作 `x`，然后重置状态并返回 `x` 的结果。你可以使用这个方法来检查定义等同性，而不赋值元变量：
  ```lean
  withoutModifyingState $ isDefEq x y
  ```
  如果 `isDefEq` 成功，它可能会为 `x` 和 `y` 赋值元变量。使用 `withoutModifyingState`，我们可以确保这种情况不会发生。
- `Lean.observing? (x : m α) : m (Option α)` 执行动作 `x`。如果 `x` 成功，`observing?` 返回其结果。如果 `x` 失败（抛出异常），`observing?` 会回溯状态并返回 `none`。这是 `tryM` 组合器的一个更具信息性的版本。
- `Lean.commitIfNoEx (x : α) : m α` 执行 `x`。如果 `x` 成功，`commitIfNoEx` 返回其结果。如果 `x` 抛出异常，`commitIfNoEx` 会回溯状态并重新抛出异常。

注意，内置的 `try ... catch ... finally` 不会执行任何回溯。因此，像这样的代码可能是错误的：

```lean
try
  doSomething
catch e =>
  doSomethingElse
```

在 `catch` 分支中，`doSomethingElse` 在包含 `doSomething` 失败前所做的修改的状态下执行。由于我们可能希望删除这些修改，我们应写成：

```lean
try
  commitIfNoEx doSomething
catch e =>
  doSomethingElse
```

另一个与 `MonadBacktrack` 相关的问题是，`restoreState` 并不会回溯*整个*状态。缓存、跟踪消息和全局名称生成器等内容不会被回溯，因此对这些状态部分的更改不会被 `restoreState` 重置。这通常是我们想要的：如果通过 `observing?` 执行的策略产生了一些跟踪消息，我们希望即使该策略失败也能看到这些消息。有关哪些内容会被回溯、哪些不会，请参阅 `Lean.Meta.SavedState.restore` 和 `Lean.Core.restore`。

在下一章中，我们将进入繁饰主题，你在本章中已经多次见到它的几个方面。我们首先讨论 Lean 的语法系统，它允许你向 Lean 的解析器添加自定义语法结构。

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
  **a)** 以非惯用方式：使用松弛绑定变量；
  **b)** 以惯用方式。
  你可以在哪种方式中使用 `Lean.mkAppN`? 还有 `Lean.Meta.mkAppM`？
11. [**构建表达式**] 创建表达式 `∀ (yellow: Nat), yellow`。
12. [**构建表达式**] 通过两种方式创建表达式 `∀ (n : Nat), n = n + 1`：
  **a)** 以非惯用方式：使用松弛绑定变量；
  **b)** 以惯用方式。
  哪种情形下可以使用 `Lean.mkApp3`？还有 `Lean.Meta.mkEq`？
13. [**构建表达式**] 以惯用方式创建表达式 `fun (f : Nat → Nat), ∀ (n : Nat), f n = f (n + 1)`。
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
