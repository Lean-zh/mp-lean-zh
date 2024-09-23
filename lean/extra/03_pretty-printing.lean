/- # 额外内容：美观打印
Lean 的美观打印器用于向用户呈现已繁饰的术语。这是通过将 `Expr` 转换回 `Syntax`，然后再转换为更高级的美观打印数据结构来完成的。这意味着 Lean 实际上不会记住它用来创建某些 `Expr` 的 `Syntax`：必须有代码告诉它如何执行此操作。

从宏观角度来看，美观打印器由三个部分组成，按列出的顺序运行：

- **[反繁饰器](https://github.com/leanprover/lean4/tree/master/src/Lean/PrettyPrinter/Delaborator)**
  这是我们主要感兴趣的部分，因为我们可以轻松地用自己的代码扩展它。它的任务是将 `Expr` 转换回 `Syntax`。
- **[括号添加器](https://github.com/leanprover/lean4/blob/master/src/Lean/PrettyPrinter/Parenthesizer.lean)**
  负责在 `Syntax` 树中添加括号，它认为在某些地方括号会有帮助。
- **[格式化器](https://github.com/leanprover/lean4/blob/master/src/Lean/PrettyPrinter/Formatter.lean)**
  负责将加了括号的 `Syntax` 树转换为包含更多美观打印信息（如显式空格）的 `Format` 对象。

## 反繁饰
顾名思义，反繁饰器在某种意义上是繁饰器的反面。反繁饰器的任务是将由繁饰器生成的 `Expr` 转换回 `Syntax`，如果再次繁饰，应该生成一个与输入行为相同的 `Expr`。

反繁饰器的类型是 `Lean.PrettyPrinter.Delaborator.Delab`。这是 `DelabM Syntax` 的别名，其中 `DelabM` 是反繁饰 monad。所有这些机制都定义在[这里](https://github.com/leanprover/lean4/blob/master/src/Lean/PrettyPrinter/Delaborator/Basic.lean)。`DelabM` 为我们提供了很多选项，您可以在文档中查看（TODO：文档链接）。这里我们只强调最相关的部分。

- 它有一个 `MonadQuotation` 实例，允许我们使用熟悉的引用语法声明 `Syntax` 对象。
- 它可以运行 `MetaM` 代码。
- 它有一个 `MonadExcept` 实例用于抛出错误。
- 它可以使用 `whenPPOption` 等函数与 `pp` 选项交互。
- 您可以使用 `SubExpr.getExpr` 获取当前的子表达式。`SubExpr` 模块中还围绕这个概念定义了整个 API。

### 创建我们自己的反繁饰器
像元编程中的许多事情一样，反繁饰器基于属性，在这种情况下是 `delab` 属性。`delab` 期望以 `Name` 作为参数，这个名称必须以 `Expr` 构造函数的名称开头，最常见的是 `const` 或 `app`。此构造函数名称后面跟着我们想要反繁饰的常量名称。例如，如果我们想以特殊方式反繁饰函数 `foo`，我们将使用 `app.foo`。让我们来看一下实际操作：
-/

import Lean

open Lean PrettyPrinter Delaborator SubExpr

def foo : Nat → Nat := fun x => 42

@[delab app.foo]
def delabFoo : Delab := do
  `(1)

#check foo -- 1 : Nat → Nat
#check foo 13 -- 1 : Nat, 整个应用同样被这样打印出来了

/-!
这显然不是一个好的反繁饰器，因为重新繁饰此 `Syntax` 不会产生相同的 `Expr`。像许多其他元编程属性一样，我们也可以重载反繁饰器：
-/

@[delab app.foo]
def delabfoo2 : Delab := do
  `(2)

#check foo -- 2 : Nat → Nat

/-!
确定使用哪个反繁饰器的机制也是相同的。反繁饰器按照注册的相反顺序依次尝试，直到其中一个没有抛出错误，表明它「不对这个 `Expr` 负责」。在反繁饰器的情况下，这是通过使用 `failure` 来完成的：
-/

@[delab app.foo]
def delabfoo3 : Delab := do
  failure
  `(3)

#check foo -- 2 : Nat → Nat, 还是 2 因为 3 失败了

/-!
为了为 `foo` 编写一个合适的反繁饰器，我们将不得不使用一些稍微高级一点的机制：
-/

@[delab app.foo]
def delabfooFinal : Delab := do
  let e ← getExpr
  guard $ e.isAppOfArity' `foo 1 -- 只能像这样反繁饰整个应用
  let fn := mkIdent `fooSpecial
  let arg ← withAppArg delab
  `($fn $arg)

#check foo 42 -- fooSpecial 42 : Nat
#check foo -- 2 : Nat → Nat, 还是 2 因为 3 失败了

/-!
你能扩展 `delabFooFinal` 来处理非完整应用的情况吗？

## 反扩展器
虽然反繁饰器非常强大，但很多情况下并不需要使用它们。如果你查看 Lean 编译器中的 `@[delab` 或 `@[builtin_delab`（编译器使用的 `delab` 属性的特殊版本，我们对此不关心），你会发现它们的出现次数很少。这是因为大多数美观打印实际上是由所谓的反扩展器完成的。与反繁饰器不同，反扩展器的类型是 `Lean.PrettyPrinter.Unexpander`，这实际上是 `Syntax → Lean.PrettyPrinter.UnexpandM Syntax` 的别名。正如你所看到的，它们是 `Syntax` 到 `Syntax` 的转换，类似于宏，区别在于它们应该是宏的逆向操作。`UnexpandM` monad 比 `DelabM` 弱得多，但它仍然具有：

- 支持语法引用的 `MonadQuotation`
- 能够抛出错误，尽管错误信息并不十分详细：`throw ()` 是唯一有效的错误

反扩展器始终针对一个常量的应用进行。它们通过 `app_unexpander` 属性注册，后面跟着该常量的名称。反扩展器在 `Expr` 经过反繁饰后被传递整个常量应用，而不包含隐式参数。让我们看看这个过程如何操作：
-/

def myid {α : Type} (x : α) := x

@[app_unexpander myid]
def unexpMyId : Unexpander
  -- 禁用语法卫生，这样我们实际上可以返回 `id`，而不涉及宏范围等。
  | `(myid $arg) => set_option hygiene false in `(id $arg)
  | `(myid) => pure $ mkIdent `id
  | _ => throw ()

#check myid 12 -- id 12 : Nat
#check myid -- id : ?m.3870 → ?m.3870

/-!
关于一些反扩展器的不错示例，你可以查看 [NotationExtra](https://github.com/leanprover/lean4/blob/master/src/Init/NotationExtra.lean)

### 项目示例
像往常一样，我们将在本章末进行一个迷你项目。这次我们将为一个迷你编程语言构建自己的反扩展器。请注意，许多定义语法的方法已经内置了生成所需的漂亮打印代码，例如 `infix` 和 `notation`（但不包括 `macro_rules`）。因此，对于简单的语法，你不需要自己手动编写这些代码。
-/

declare_syntax_cat lang
syntax num   : lang
syntax ident : lang
syntax "let " ident " := " lang " in " lang: lang
syntax "[Lang| " lang "]" : term

inductive LangExpr
  | numConst : Nat → LangExpr
  | ident    : String → LangExpr
  | letE     : String → LangExpr → LangExpr → LangExpr

macro_rules
  | `([Lang| $x:num ]) => `(LangExpr.numConst $x)
  | `([Lang| $x:ident]) => `(LangExpr.ident $(Lean.quote (toString x.getId)))
  | `([Lang| let $x:ident := $v:lang in $b:lang]) => `(LangExpr.letE $(Lean.quote (toString x.getId)) [Lang| $v] [Lang| $b])

instance : Coe NumLit (TSyntax `lang) where
  coe s := ⟨s.raw⟩

instance : Coe Ident (TSyntax `lang) where
  coe s := ⟨s.raw⟩

-- LangExpr.letE "foo" (LangExpr.numConst 12)
--   (LangExpr.letE "bar" (LangExpr.ident "foo") (LangExpr.ident "foo")) : LangExpr
#check [Lang|
  let foo := 12 in
  let bar := foo in
  foo
]

/-!
正如你所见，目前的漂亮打印输出相当难看。我们可以通过使用反扩展器来改进它：
-/

@[app_unexpander LangExpr.numConst]
def unexpandNumConst : Unexpander
  | `(LangExpr.numConst $x:num) => `([Lang| $x])
  | _ => throw ()

@[app_unexpander LangExpr.ident]
def unexpandIdent : Unexpander
  | `(LangExpr.ident $x:str) =>
    let str := x.getString
    let name := mkIdent $ Name.mkSimple str
    `([Lang| $name])
  | _ => throw ()

@[app_unexpander LangExpr.letE]
def unexpandLet : Unexpander
  | `(LangExpr.letE $x:str [Lang| $v:lang] [Lang| $b:lang]) =>
    let str := x.getString
    let name := mkIdent $ Name.mkSimple str
    `([Lang| let $name := $v in $b])
  | _ => throw ()

-- [Lang| let foo := 12 in foo] : LangExpr
#check [Lang|
  let foo := 12 in foo
]

-- [Lang| let foo := 12 in let bar := foo in foo] : LangExpr
#check [Lang|
  let foo := 12 in
  let bar := foo in
  foo
]

/-!
这样就好多了！一如既往，我们鼓励你自己扩展语言，比如添加带括号的表达式、更多的数据值、对 `term` 的引用，或其他你能想到的内容。
-/
