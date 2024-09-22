/-
# 宏

## 什么是宏
Lean 中的宏是 `Syntax → MacroM Syntax` 类型的函数。`MacroM` 是宏的单子，它允许宏拥有一些静态保证，我们将在下一节中讨论这些保证，目前你可以暂时忽略它。

宏作为特定语法声明的处理器使用 `macro` 属性来声明。编译器会在实际分析输入之前自动将这些函数应用到语法上。这意味着我们只需声明一个特定名称的语法，并将一个类型为 `Lean.Macro` 的函数绑定到它上面。让我们尝试重现 `Syntax` 章节中的 `LXOR` 符号：
-/

import Lean

open Lean

syntax:10 (name := lxor) term:10 " LXOR " term:11 : term

@[macro lxor] def lxorImpl : Macro
  | `($l:term LXOR $r:term) => `(!$l && $r) -- 我们可以使用引号机制在宏中创建 `Syntax`
  | _ => Macro.throwUnsupported

#eval true LXOR true -- false
#eval true LXOR false -- false
#eval false LXOR true -- true
#eval false LXOR false -- false

/-
这非常简单！宏可以使用 `Macro.throwUnsupported` 函数表示它“不认为自己负责处理这种语法”。在这个例子中，它仅仅用于填充一个永远不应该被触发的通配符模式。

事实上，如果我们愿意，我们可以为相同的语法编写多个宏。它们将一个接一个地尝试（后编写的宏具有更高优先级）直到某个宏要么抛出真正的错误（使用 `Macro.throwError`），要么成功，也就是说它没有 `Macro.throwUnsupported`。让我们看看这个功能的实际效果：
-/

@[macro lxor] def lxorImpl2 : Macro
  -- 处理左右两侧为这些特定标识符的特殊情况
  | `(true LXOR true) => `(true)
  | _ => Macro.throwUnsupported

#eval true LXOR true -- true，由新宏处理
#eval true LXOR false -- false，仍由旧宏处理

/-
这种能力显然非常强大！在不经过深思熟虑的情况下不要轻易使用它，因为它可能在编写代码时引入奇怪的行为。以下例子展示了这种奇怪的行为：
-/

#eval true LXOR true -- true，由新宏处理

def foo := true
#eval foo LXOR foo -- false，由旧宏处理，毕竟标识符的名字不同

/-
如果不知道这个宏是如何实现的，那么调试这个问题的开发者可能会非常困惑。

关于何时应该使用宏而不是其他机制（如繁饰），经验法则是：当你开始构建真正的逻辑时，例如上面第二个宏中的逻辑，它很可能不应该是一个宏，而应该是一个繁饰器（繁饰器将在繁饰章节中进行讲解）。这意味着理想情况下，我们希望将宏用于简单的语法到语法的转换，人类也可以轻松地手动编写这些转换，但可能嫌麻烦。

## 简化宏声明
现在我们了解了宏的基础知识以及如何编写宏，我们可以来看一些稍微自动化的方式（事实上，接下来要介绍的所有方式都是通过宏自己实现的）。

首先是 `macro_rules`，它基本上是对我们上面编写的函数的语法糖，例如：
-/

syntax:10 term:10 " RXOR " term:11 : term

macro_rules
  | `($l:term RXOR $r:term) => `($l && !$r)

/-
它自动完成了许多事情：
- 语法声明的名称
- `macro` 属性的注册
- `throwUnsupported` 的通配符

除此之外，它就像一个使用模式匹配语法的函数一样工作，理论上我们可以在右侧编写任意复杂的宏函数。

如果你觉得这还不够简短，可以使用 `macro` 语法糖：
-/

macro l:term:10 " ⊕ " r:term:11 : term => `((!$l && $r) || ($l && !$r))

#eval true ⊕ true -- false
#eval true ⊕ false -- true
#eval false ⊕ true -- true
#eval false ⊕ false -- false


/-
如你所见，`macro` 已经非常接近 `notation` 了：
- 它为我们进行了语法声明
- 它自动生成了一个 `macro_rules` 风格的函数来匹配语法

当然，它们之间也有一些区别：
- `notation` 仅限于 `term` 语法类别
- `notation` 不能在右侧包含任意的宏代码

## `Syntax` 引号
### 基础知识
到目前为止，我们使用了 `` `(foo $bar) `` 语法来创建和匹配 `Syntax` 对象，但现在是时候进行完整的解释了，因为它在进阶的语法中至关重要。

首先我们称 `` `() `` 语法为 `Syntax` 引号。当我们将变量插入到语法引号中，如：`` `($x) ``，我们称 `$x` 部分为反引号（anti-quotation）。当我们像这样插入 `x` 时，要求 `x` 的类型为 `TSyntax y`，其中 `y` 是某种语法类别的名称。Lean 编译器实际上足够智能，能够推断出允许在此处使用的语法类别。因此，你有时可能会看到如下形式的错误：
```
application type mismatch 应用类型不匹配
  x.raw
argument 参数
  x
has type 类型为
  TSyntax `a : Type
but is expected to have type 但期望的类型为
  TSyntax `b : Type
```
如果你确信来自 `a` 语法类别的元素可以用作 `b`，你可以声明如下形式的类型转换：
-/

instance : Coe (TSyntax `a) (TSyntax `b) where
  coe s := ⟨s.raw⟩

/-!
这将允许 Lean 自动执行类型转换。如果你发现你的 `a` 不能在此处替代 `b`，恭喜你，你刚刚发现了你的 `Syntax` 函数中的一个 bug。类似于 Lean 编译器，你还可以声明特定于某些 `TSyntax` 变体的函数。例如，如我们在语法章节中所见，已经存在如下函数：
-/

#check TSyntax.getNat -- TSyntax.getNat : TSyntax numLitKind → Nat

/-!
此函数不会发生错误，因为我们知道传递给它的 `Syntax` 是一个数字字面量，因此可以自然地转换为 `Nat`。

如果我们在模式匹配中使用反引号语法，如前面提到的，它将为我们提供类型为 `TSyntax y` 的变量 `x`，其中 `y` 是适合我们模式匹配位置的语法类别名称。如果出于某种原因我们想要将字面量 `$x` 插入到 `Syntax` 中，例如用于创建宏的宏，我们可以使用 `` `($$x) `` 来取消反引号（类似C等语言中的两次反斜杠转义）。

如果我们希望指定 `x` 的语法类型，可以使用 `` `($x:term) ``，其中 `term` 可以替换为任何其他有效的语法类别（如 `command`）或解析器（如 `ident`）。

到目前为止，这只是对我们在语法章节中以及本章至今所见的直观概念的更正式解释，接下来我们将讨论一些更高级的反引号用法。

### 高级反引号
为了方便起见，我们还可以以类似格式字符串的方式使用反引号：`` `($(mkIdent `c)) `` 与 `` let x := mkIdent `c; `($x) `` 是等价的。

此外，有时我们处理的并不是基本的 `Syntax`，而是更复杂的数据结构中包含的 `Syntax`，最典型的是 `Array (TSyntax c)` 或 `TSepArray c s`。其中 `TSepArray c s` 是一个 `Syntax` 特定类型，它是当我们在使用分隔符 `s` 来分隔 `c` 类别的元素时通过模式匹配得到的。例如，如果我们使用 `$xs,*` 进行匹配，`xs` 的类型将是 `TSepArray c ","`。而匹配时没有特定分隔符（即空白）时，如 `$xs*`，我们将得到 `Array (TSyntax c)`。

如果我们正在处理 `xs : Array (TSyntax c)` 并且想要将其插入到引号中，有两种主要方法可以实现：
1. 使用分隔符插入，最常见的是逗号：`` `($xs,*) ``。这也是插入 `TSepArray c ",""` 的方式。
2. 直接无分隔符插入（TODO）：`` `() ``
-/

-- 如果可能的话，在语法上从元组中切掉第一个元素
syntax "cut_tuple " "(" term ", " term,+ ")" : term

macro_rules
  -- 切掉一对中的一个元素是不可能的，因为这不会形成元组
  | `(cut_tuple ($x, $y)) => `(($x, $y))
  | `(cut_tuple ($x, $y, $xs,*)) => `(($y, $xs,*))

#check cut_tuple (1, 2) -- (1, 2) : Nat × Nat
#check cut_tuple (1, 2, 3) -- (2, 3) : Nat × Nat

/-!
本节的最后一部分将介绍所谓的「反引号拼接」。反引号拼接有两种类型，首先是可选拼接。例如，我们可能会声明一个带有可选填参数的语法，比如我们自己的 `let`。（现实例子是，仿写另一种函数式语言中的 `let`）：
-/

syntax "mylet " ident (" : " term)? " := " term " in " term : term

/-!
这里涉及一个可选填参数 `(" : " term)?`，用户可以通过它定义左边项的类型。按照我们目前掌握的方法，我们需要编写两个 `macro_rules`，一个处理带可选填参数的情况，一个处理不带的情况。然而，语法翻译的其余部分在有无可选填参数的情况下完全相同，因此我们可以使用拼接来同时定义两种情况：
-/

macro_rules
  | `(mylet $x $[: $ty]? := $val in $body) => `(let $x $[: $ty]? := $val; $body)

/-!
这里的 `$[...]?` 部分就是拼接，它的作用基本上是说「如果这部分语法不存在，那么就忽略右侧涉及的反引号变量」。所以现在我们可以在无论有无类型说明的情况下运行这个语法：
-/

#eval mylet x := 5 in x - 10 -- 0，因为 `Nat` 的减法行为
#eval mylet x : Int := 5 in x - 10 -- -5，因为现在它是 `Int` 类型

/-!
第二种拼接可能会让读者联想到例如在 Python 中看到的列表推导式。演示：
-/

-- 对每个列表元素执行函数
syntax "foreach " "[" term,* "]" term : term

macro_rules
  | `(foreach [ $[$x:term],* ] $func:term) => `(let f := $func; [ $[f $x],* ])

#eval foreach [1,2,3,4] (Nat.add 2) -- [3, 4, 5, 6]

/-!
在这种情况下，`$[...],*` 部分是拼接。在匹配部分，它会尝试根据我们定义的模式进行重复匹配（根据我们指定的分隔符）。然而，不同于常规的分隔符匹配，它不会返回 `Array` 或 `SepArray`，而是允许我们在右侧写另一个拼接，每次匹配到我们指定的模式时，该拼接都会被计算，并使用每次匹配中的特定值。
-/

/-!
## 卫生问题及其解决方案
如果你熟悉其他语言（如 C）的宏系统，你可能已经听说过所谓的宏卫生问题。宏卫生问题指的是，当宏引入的标识符与它包含的某些语法中的标识符发生冲突时。例如:
-/

-- 应用这个宏会生成一个绑定了新标识符 `x` 的函数。
macro "const" e:term : term => `(fun x => $e)

-- 但是 `x` 也可以由用户定义
def x : Nat := 42

-- 编译器在替换 `$e` 时应该使用哪个 `x`？
#eval (const x) 10 -- 42

/-
鉴于宏只执行语法转换，你可能会预期上面的 `eval` 返回 10 而不是 42：毕竟，结果语法应该是 `(fun x => x) 10`。虽然这显然不是作者的本意，但在更原始的宏系统（如 C 语言的宏系统）中，这就是会发生的情况。那么 Lean 是如何避免这些宏卫生问题的呢？你可以在出色的论文 [Beyond Notations](https://lmcs.episciences.org/9362/pdf) 中详细阅读 Lean 的这个思想和实现。我们这里只做一个概述，因为具体细节对实际使用没有那么大的意义。

《Beyond Notations》提出的思想归结为一个叫做「宏作用域」（macro scopes）的概念。每当一个新的宏被调用时，一个新的宏作用域（基本上是一个唯一的数字）会被添加到当前所有活跃宏作用域的列表中。当目前的宏引入一个新标识符时，实际上被添加的是以下形式的标识符：
```
<实际名称>._@.(<模块名称>.<作用域>)*.<模块名称>._hyg.<作用域>
```
例如，如果模块名称是 `Init.Data.List.Basic`，名称是 `foo.bla`，宏作用域是 [2, 5]，我们得到的标识符是：
```
foo.bla._@.Init.Data.List.Basic._hyg.2.5
```
由于宏作用域是唯一的数字，附加在名称末尾的宏作用域列表将在所有宏调用中保持唯一，因此像上面那样的宏卫生问题是不可能出现的。

如果你想知道为什么除了宏作用域之外还有其他内容，那是因为我们可能需要组合来自不同文件/模块的作用域。当前处理的主模块总是最右边的一个。这种情况可能发生在我们执行从当前文件导入的文件中生成的宏时。例如：
```
foo.bla._@.Init.Data.List.Basic.2.1.Init.Lean.Expr_hyg.4
```
末尾的 `_hyg` 分隔符只是为了提高 `Lean.Name.hasMacroScopes` 函数的性能 -- 这种格式没有它也能工作。

以上有很多技术细节。你不需要理解它们也可以使用宏，只需记住 Lean 不会允许像 `const` 示例中那样的名称冲突问题。

请注意，这适用于**所有**使用语法引用引入的名称，也就是说，如果你编写了一个生成以下代码的宏：
```
`(def foo := 1)
```
用户将无法访问 `foo`，因为这个名称会受到卫生规则的影响。幸运的是，有一种方法可以绕过这个问题。你可以使用 `mkIdent` 来生成一个原始标识符，例如：
```
`(def $(mkIdent `foo) := 1)
```
在这种情况下，它将不会受宏卫生规则影响，用户可以访问该名称。

## `MonadQuotation` 和 `MonadRef`

基于上述宏卫生机制的描述，出现了一个有趣的问题：我们如何知道当前的宏作用域列表到底是什么？毕竟，在上面定义的宏函数中，并没有显式地传递这些作用域的过程。正如在函数式编程中常见的那样，当我们需要跟踪一些额外的状态（比如宏作用域）时，通常会使用一个单子来处理。在这里也是如此，不过有一点小小的不同。

这里并不是仅为单个 `MacroM` 单子实现这个功能，而是通过一个叫做 `MonadQuotation` 的类型类抽象出跟踪宏作用域的通用概念。这样，任何其他单子只需实现这个类型类，就可以轻松提供这种带有卫生性的 `Syntax` 创建机制。

这也是为什么我们虽然可以使用 `` `(syntax) `` 对语法进行模式匹配，但不能在纯函数中直接用相同的语法创建 `Syntax` 的原因：因为没有涉及到实现了 `MonadQuotation` 的 `Monad` 来跟踪宏作用域。

现在让我们简要看看 `MonadQuotation` 类型类：
-/

namespace Playground

class MonadRef (m : Type → Type) where
  getRef      : m Syntax
  withRef {α} : Syntax → m α → m α

class MonadQuotation (m : Type → Type) extends MonadRef m where
  getCurrMacroScope : m MacroScope
  getMainModule     : m Name
  withFreshMacroScope {α : Type} : m α → m α

end Playground

/-
由于 `MonadQuotation` 基于 `MonadRef`，我们先来看看 `MonadRef`。其核心思想非常简单：`MonadRef` 作为 `Monad` 类型类的扩展，它提供了以下功能：

- 通过 `getRef` 获取对 `Syntax` 值的引用。
- 使用 `withRef` 在新的 `Syntax` 引用下执行某个 monadic 操作 `m α`。

单独来看，`MonadRef` 并不是特别有趣，但一旦与 `MonadQuotation` 结合，它就有了意义。

如你所见，`MonadQuotation` 扩展了 `MonadRef`，并增加了三个新函数：

- `getCurrMacroScope`：获取最新创建的 `MacroScope`。
- `getMainModule`：获取主模块的名称。这两个函数用于创建上面提到的带有卫生性的标识符。
- `withFreshMacroScope`：计算下一个宏作用域，并运行某些执行语法引用的计算 `m α`，以避免名称冲突。虽然这主要用于内部在新宏调用发生时调用，但在我们编写自己的宏时有时也有用，比如当我们反复生成某些语法块时，想要避免名称冲突。

`MonadRef` 在这里的作用是 Lean 需要一种方式来向用户指示某些位置的错误。一个没有在 `Syntax` 章节介绍的内容是，类型为 `Syntax` 的值实际上携带了它们在文件中的位置信息。当检测到错误时，通常会绑定到一个 `Syntax` 值上，以便 Lean 能够在文件中准确指示错误位置。

当使用 `withFreshMacroScope` 时，Lean 会将 `getRef` 的结果位置应用到每个引入的符号上，从而生成更准确的错误位置信息，而不是没有位置信息。

为了看到错误定位的实际效果，我们可以写一个小的宏来展示这个功能：
-/

syntax "error_position" ident : term

macro_rules
  | `(error_position all) => Macro.throwError "Ahhh"
  -- `%$tk` 语法给 `%` 之前的东西命名为 `tk`，本例中是 `error_position`。
  | `(error_position%$tk first) => withRef tk (Macro.throwError "Ahhh")

#check_failure error_position all -- 错误在 `error_position all` 处显示
#check_failure error_position first -- 错误仅在 `error_position` 处显示

/-
显然，以这种方式控制错误的位置对提供良好的用户体验非常重要。

## 项目示例
作为本节的最终迷你项目，我们将以稍微更高级的方式重建语法章节中的算术 DSL，这次我们将使用宏来实现，从而可以将其完全集成到 Lean 语法中。
-/
declare_syntax_cat arith

syntax num : arith
syntax arith "-" arith : arith
syntax arith "+" arith : arith
syntax "(" arith ")" : arith
syntax "[Arith|" arith "]" : term

macro_rules
  | `([Arith| $x:num]) => `($x)
  | `([Arith| $x:arith + $y:arith]) => `([Arith| $x] + [Arith| $y]) -- 递归宏是可以实现的
  | `([Arith| $x:arith - $y:arith]) => `([Arith| $x] - [Arith| $y])
  | `([Arith| ($x:arith)]) => `([Arith| $x])

#eval [Arith| (12 + 3) - 4] -- 11

/-!
如果你想构建更复杂的内容，比如包含变量的表达式，或许可以考虑使用宏来构建一个归纳类型。一旦你将算术表达式作为归纳类型，你就可以编写一个函数，该函数接受某种形式的变量赋值并对给定表达式进行求值。你还可以尝试使用一些特殊的语法将任意 `term` 嵌入到你的算术语言中，或者发挥你的想象力做其他事情。

## 更复杂的示例
### 绑定（续）
正如在语法章节中所承诺的，这里是绑定 2.0。我们将从重新引入集合理论开始：
-/
def Set (α : Type u) := α → Prop
def Set.mem (x : α) (X : Set α) : Prop := X x

-- 集成到已经存在的成员符号类中
instance : Membership α (Set α) where
  mem := Set.mem

def Set.empty : Set α := λ _ => False

-- 基本的 "所有满足某条件的元素" 函数，用于符号表示法
def setOf {α : Type} (p : α → Prop) : Set α := p

/-!
本节的目标是允许 `{x : X | p x}` 和 `{x ∈ X, p x}` 的表示法。原则上，有两种方法可以实现：
1. 为每种可能的绑定变量的方式定义语法和宏
2. 定义一种可以在其他绑定构造（例如 `Σ` 或 `Π`）中复用的绑定符号语法类别，并为 `{ | }` 的情况实现宏

在本节中，我们将采用方法 2，因为它更易于复用。
-/

declare_syntax_cat binder_construct
syntax "{" binder_construct "|" term "}" : term

/-!
现在我们来定义两个我们感兴趣的绑定符号构造：
-/
syntax ident " : " term : binder_construct
syntax ident " ∈ " term : binder_construct

/-!
最后，我们为语法扩展定义宏：
-/

macro_rules
  | `({ $var:ident : $ty:term | $body:term }) => `(setOf (fun ($var : $ty) => $body))
  | `({ $var:ident ∈ $s:term | $body:term }) => `(setOf (fun $var => $var ∈ $s ∧ $body))

/-
以下是使用新语法的示例：
-/
-- 旧示例，使用更好的语法：
#check { x : Nat | x ≤ 1 } -- setOf fun x => x ≤ 1 : Set Nat

example : 1 ∈ { y : Nat | y ≤ 1 } := by simp[Membership.mem, Set.mem, setOf]
example : 2 ∈ { y : Nat | y ≤ 3 ∧ 1 ≤ y } := by simp[Membership.mem, Set.mem, setOf]

-- 新示例：
def oneSet : Set Nat := λ x => x = 1
#check { x ∈ oneSet | 10 ≤ x } -- setOf fun x => x ∈ oneSet ∧ 10 ≤ x : Set Nat

example : ∀ x, ¬(x ∈ { y ∈ oneSet | y ≠ 1 }) := by
  intro x h
  -- h : x ∈ setOf fun y => y ∈ oneSet ∧ y ≠ 1
  -- ⊢ False
  cases h
  -- : x ∈ oneSet
  -- : x ≠ 1
  contradiction


/-!
## 拓展阅读
如果你想了解更多关于宏的信息，可以阅读：
- API 文档：待补充链接
- 源代码：[Init.Prelude](https://github.com/leanprover/lean4/blob/master/src/Init/Prelude.lean) 的底层部分，如你所见，由于它们在构建语法中非常重要，因此在 Lean 中被很早声明
- 前面提到的论文 [Beyond Notations](https://lmcs.episciences.org/9362/pdf)
-/
