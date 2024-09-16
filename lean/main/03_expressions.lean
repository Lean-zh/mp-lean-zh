/-
# 表达式

表达式（类型为 `Expr` 的项）是 Lean 程序的抽象语法树。这意味着每个可以用 Lean 编写的项都有一个对应的 `Expr`。例如，函数应用 `f e` 由表达式 `Expr.app ⟦f⟧ ⟦e⟧` 表示，其中 `⟦f⟧` 是 `f` 的表示，而 `⟦e⟧` 是 `e` 的表示。类似地，项 `Nat` 由表达式 ``Expr.const `Nat []`` 表示。（反引号和空列表将在下面讨论。）

Lean 策略块的最终目的是生成一个项，作为我们想要证明的定理的证明。因此，策略的目的是生成正确类型的 `Expr`（的一部分）。因此，许多元编程归结为操纵表达式：构造新的表达式并拆分现有的表达式。

一旦策略块完成，`Expr` 就会被发送到内核，内核会检查它是否类型正确，以及它是否真的具有定理所声称的类型。因此，策略错误并不致命：如果你犯了一个错误，内核最终会发现它。但是，许多内部 Lean 函数也假设表达式是类型正确的，因此你可能会在表达式到达内核之前就让 Lean 崩溃。为了避免这种情况，Lean 提供了许多有助于操作表达式的函数。本章和下一章将介绍最重要的函数。

让我们具体一点，看看 [`Expr`](https://github.com/leanprover/lean4/blob/master/src/Lean/Expr.lean) 类型：
-/

import Lean

namespace Playground

inductive Expr where
  | bvar    : Nat → Expr                              -- 绑定变量 bound variables
  | fvar    : FVarId → Expr                           -- 自由变量 free variables
  | mvar    : MVarId → Expr                           -- 元变量 meta variables
  | sort    : Level → Expr                            -- Sort
  | const   : Name → List Level → Expr                -- 常量 constants
  | app     : Expr → Expr → Expr                      -- 应用 application
  | lam     : Name → Expr → Expr → BinderInfo → Expr  -- lambda抽象 lambda abstraction
  | forallE : Name → Expr → Expr → BinderInfo → Expr  -- (依值) 箭头(dependent) arrow
  | letE    : Name → Expr → Expr → Expr → Bool → Expr -- let 表达式
  -- 没那么必要的构造器：
  | lit     : Literal → Expr                          -- 字面量 literals
  | mdata   : MData → Expr → Expr                     -- 元变量 metadata
  | proj    : Name → Nat → Expr → Expr                -- 投影 projection

end Playground
/-!
这些构造函数各自在做什么？

- `bvar` 是一个 **绑定变量**。例如，`fun x => x + 2` 或 `∑ x, x²` 中的 `x`。这是表达式中变量的任何出现，其中有一个绑定器。为什么参数是 `Nat`？这称为 de Bruijn 索引，稍后将解释。您可以通过查看绑定变量的绑定器来确定绑定变量的类型，因为绑定器始终具有其类型信息。
- `fvar` 是一个 **自由变量**。这些是不受绑定器绑定的变量。一个例子是 `x + 2` 中的 `x`。请注意，您不能只看一个自由变量 `x` 并知道它的类型是什么，需要有一个包含 `x` 及其类型的声明的语境。自由变量有一个 ID，它会告诉您在 `LocalContext` 中查找它的位置。在 Lean 3 中，自由变量也被称为「局部变量」。
- `mvar` 是一个 **元变量**。稍后将有更多关于它的内容，但您可以将其视为表达式中的占位符或「洞」，需要在稍后填充。
- `sort` 用于 `Type u`、`Prop` 等。
- `const` 是 Lean 文件中先前定义的常量。
- `app` 是一个函数应用。多参数是用部分应用（partial application）实现的，例如：`f x y ↝ app (app f x) y`。
- `lam n t b` 是一个 lambda 表达式（`fun ($n : $t) => $b`）。`b` 参数称为 **函数体**。请注意，您必须提供要绑定的变量的类型。
- `forallE n t b` 是一个依值箭头表达式（`($n : $t) → $b`）。这有时也称为 Π 类型或 Π 表达式，并且通常写为 `∀ $n : $t, $b`。请注意，非依值箭头 `α → β` 是 `(a : α) → β` 的一个特例，其中 `β` 不依赖于 `a`。`forallE` 末尾的 `E` 是为了将其与 `forall` 关键字区分开来。
- `letE n t v b` 是一个 **let 绑定器**（`let ($n : $t) := $v in $b`）。
- `lit` 是一个 **字面量** (Literal)，这是一个数字或字符串文字，如 `4` 或 `"hello world"`。字面量有助于提高性能：我们不想将表达式 `(10000 : Nat)` 表示为 `Nat.succ $ ... $ Nat.succ Nat.zero`。
- `mdata` 只是一种在表达式中存储可能有用的额外信息的方式，不会改变表达式的性质。
- `proj` 用于投影。假设您有一个结构，例如 `p : α × β`，投影 `π₁ p` 不是存储为 `app π₁ p`，而表示为 `proj Prod 0 p`。这是出于效率原因（[todo] 引证）。

另外，您可以编写许多没有明显对应的 `Expr` 的 Lean 程序。例如， `match` 语句、`do` 块或 `by` 块等等。这些构造确实必须通过繁饰器首先转换为表达式，在后面的章节讨论。这种设置的好处是，一旦完成到 `Expr`的转换，我们就可以使用相对简单的结构。（缺点是从 `Expr` 返回到高级 Lean 程序可能具有挑战性。）

繁饰器还会填充您可能从 Lean 程序中省略的任何隐式或类型类实例参数。因此，在 `Expr` 级别，常量始终应用于所有参数，无论是否隐式。这样做的好处是可以获得大量从源代码中不明显的信息，坏处是构建 `Expr` 时，您必须自己提供任何隐式或实例参数）。

## De Bruijn 索引

考虑以下 lambda 表达式 `(λ f x => f x x) (λ x y => x + y) 5`，化简时会在变量 `x` 中遇到冲突。

为了避免变量名称冲突，`Expr` 使用了一个称为 __de Bruijn 索引__ 的巧妙技巧。在 de Bruijn 索引中，每个由 `lam` 或 `forallE` 绑定的变量都会转换为数字 `#n`。该数字表示我们应该在 `Expr` 树上查找多少个绑定器才能找到绑定此变量的绑定器。因此，我们上面的例子将变成（为了简洁起见，现在在类型参数中放置通配符 `_`）：

``app (app (lam `f _ (lam `x _ (app (app #1 #0) #0))) (lam `x _ (lam `y _ (app (app plus #1) #0)))) five``

现在我们在执行β-规约时不需要重命名变量。我们还可以轻松检查两个包含绑定表达式的 `Expr` 是否相等。这就是为什么 `bvar` 的类型签名是 `Nat → Expr` 而不是 `Name → Expr`。

如果 de Bruijn 指标对于其前面的绑定器数量来说太大，我们说它是一个 __松弛的 `bvar`__；否则我们说它是 __绑定的__。例如，在表达式 ``lam `x _ (app #0 #1)`` 中，`bvar` `#0` 由前面的绑定器绑定，而 `#1` 是松弛的。 Lean 将所有 de Bruijn 索引称为 `bvar`（「绑定变量」），这隐含了一种理念：除了一些非常低级的函数之外，Lean 期望表达式不包含任何松弛的 `bvar`。相反，每当我们想要引入一个松弛的 `bvar` 时，我们都会立即将其转换为 `fvar`（「自由变量」）。下一章将讨论其具体工作原理。

如果表达式中没有松弛的 `bvar`，我们称该表达式为 __闭的__。用 `Expr` 替换所有松弛的 `bvar` 实例的过程称为 __实例化__（instantiation）。反之称为**抽象化**（abstraction）。

如果您熟悉变量的标准术语，Lean 的术语可能会令人困惑，对应关系：Lean 的`bvar`通常被称为「变量」；Lean 的「松弛」通常称为「自由」；而 Lean 的`fvar`或许可以被称为「局部假设」。

## 宇宙等级

一些表达式涉及宇宙等级，由 `Lean.Level` 类型表示。宇宙等级是一个自然数、一个宇宙参数（通过 `universe` 声明引入）、一个宇宙元变量或两个宇宙中的最大值。它们与两种表达式相关。

首先，sort由 `Expr.sort u` 表示，其中 `u` 是 `Level`。`Prop` 是 `sort Level.zero`；`Type` 是 `sort (Level.succ Level.zero)`。

其次，宇宙多态常量具有宇宙参数。宇宙多态常量是其类型包含宇宙参数的常量。例如，`List.map` 函数是宇宙多态的，如 `pp.universes` 美观打印选项所示：
-/

set_option pp.universes true in
#check @List.map

/-!
`List.map` 后面的 `.{u_1,u_2}` 后缀表示 `List.map` 有两个宇宙参数，`u_1` 和 `u_2`。`List`（本身是一个宇宙多态常量）后面的 `.{u_1}` 后缀表示 `List` 应用于宇宙参数 `u_1`，`.{u_2}` 也是如此。

事实上，每当您使用宇宙多态常量时，都必须将其应用于正确的宇宙参数。此应用由 `Expr.const` 的 `List Level` 参数表示。当我们编写常规 Lean 代码时，Lean 会自动推断宇宙，因此我们不需要过多考虑它们。但是当我们构造 `Expr` 时，我们必须小心将每个宇宙多态常量应用于正确的宇宙参数。

## 构造表达式

### 常量

我们可以构造的最简单的表达式是常量。我们使用 `const` 构造器并为其指定一个名称和一个宇宙等级列表。我们的大多数示例仅涉及非宇宙多态常量，在这种情况下宇宙等级列表为空。

反引号标识 `Name` 类型的项，也就是一个名称。名称可以任取，但有时你需要引用已定义的常量，此时可以用双反引号写名称。双反引号可以检查名称是否真的引用了已定义的常量，有助于避免拼写错误。
-/

open Lean

def z' := Expr.const `Nat.zero []
#eval z' -- Lean.Expr.const `Nat.zero []

def z := Expr.const ``Nat.zero []
#eval z -- Lean.Expr.const `Nat.zero []

/-
双反引号还可以解析给定的名称。下例演示了这种机制。第一个表达式 `z₁` 是不安全的：如果我们在 `Nat` 命名空间未开放的上下文中使用它，Lean 会抱怨环境中没有名为 `zero` 的常量。相比之下，第二个表达式 `z₂` 包含已有的名称 `Nat.zero`，不存在这个问题。
-/

open Nat

def z₁ := Expr.const `zero []
#eval z₁ -- Lean.Expr.const `zero []

def z₂ := Expr.const ``zero []
#eval z₂ -- Lean.Expr.const `Nat.zero []

/-
### 函数应用

我们考虑的下一类表达式是函数应用。这些可以使用 `app` 构造器构建，其中第一个参数是函数表达式，第二个参数是表示函数的参数的表达式。

以下是两个示例。第一个只是将一个常量应用于另一个常量。第二个是递归定义，给出一个作为自然数函数的表达式。
-/

def one := Expr.app (.const ``Nat.succ []) z -- Expr.const可以省略为.const
#eval one
-- Lean.Expr.app (Lean.Expr.const `Nat.succ []) (Lean.Expr.const `Nat.zero [])

def natExpr: Nat → Expr
| 0     => z
| n + 1 => .app (.const ``Nat.succ []) (natExpr n)

/-
 `app` 的变体 `mkAppN` 支持多参数应用。
-/

def sumExpr : Nat → Nat → Expr
| n, m => mkAppN (.const ``Nat.add []) #[natExpr n, natExpr m]

/-
最后两个函数的 `#eval` 输出表达式非常大，您可以自己试试看。

### lambda 抽象

接下来，我们使用构造器 `lam` 来构造一个简单的函数，该函数接受任何自然数 `x` 并返回 `Nat.zero`。回忆一下`lam`构造器的类型是`Name → Expr → Expr → BinderInfo → Expr`，第一个`Expr`是`Name`对应的参数的变量类型，第二个`Expr`是函数体。参数 `BinderInfo.default` 表示 `x` 是一个显式参数（而不是隐式`BinderInfo.implicit`或类型类参数）。
-/

def constZero : Expr :=
  .lam `x (.const ``Nat []) (.const ``Nat.zero []) BinderInfo.default

#eval constZero
-- Lean.Expr.lam `x (Lean.Expr.const `Nat []) (Lean.Expr.const `Nat.zero [])
--   (Lean.BinderInfo.default)

/-!
下面是更复杂的例子，还涉及到宇宙级别，这里是表示 `List.map (λ x => Nat.add x 1) []` 的 `Expr`（分成几个定义以使其更具可读性）：
-/

def nat : Expr := .const ``Nat []

def addOne : Expr :=
  .lam `x nat
    (mkAppN (.const ``Nat.add []) #[.bvar 0, mkNatLit 1])
    BinderInfo.default

def mapAddOneNil : Expr :=
  mkAppN (.const ``List.map [levelZero, levelZero])
    #[nat, nat, addOne, .app (.const ``List.nil [levelZero]) nat]

/-!
通过一个小技巧（详见[繁饰](#./07_elaboration.lean)一章），我们可以将 `Expr` 转换为 Lean 项，这样可以更轻松地检查它。
-/

elab "mapAddOneNil" : term => return mapAddOneNil

#check mapAddOneNil
-- List.map (fun x => Nat.add x 1) [] : List Nat

set_option pp.universes true in
set_option pp.explicit true in
#check mapAddOneNil
-- @List.map.{0, 0} Nat Nat (fun x => x.add 1) (@List.nil.{0} Nat) : List.{0} Nat

#reduce mapAddOneNil
-- []

/-
在下一章中，我们将探索 `MetaM` 单子，它具有更方便地构建和销毁更大的表达式和其它一些功能。

## 习题

1. 利用 `Expr.app` 创建表达式 `1 + 2`
2. 利用 `Lean.mkAppN` 创建表达式 `1 + 2`
3. 创建表达式 `fun x => 1 + x`
4. [**De Bruijn 索引**] 创建表达式 `fun a, fun b, fun c, (b * a) + c`
5. 创建表达式 `fun x y => x + y`
6. 创建表达式 `fun x, String.append "hello, " x`
7. 创建表达式 `∀ x : Prop, x ∧ x`
8. 创建表达式 `Nat → String`
9. 创建表达式 `fun (p : Prop) => (λ hP : p => hP)`
10. [**Universe levels**] 创建表达式 `Type 6`
-/
