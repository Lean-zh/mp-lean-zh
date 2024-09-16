/-
# 概述

在本章中，我们将概述 Lean 编译过程中涉及的主要步骤，包括解析（parsing）、繁饰（elaboration）和求值（evaluation）。正如介绍中提到的，Lean 中的元编程需要深入这个过程的核心。我们将探索所涉及的基本对象 `Expr` 和 `Syntax`，了解它们的含义，并发现如何将一个对象转换为另一个对象（并转换回来！）。

后面的章节会介绍细节，你可以之后回顾本章，以提醒自己这些组件是如何组合在一起的。

## 与编译器的连接

Lean 中的元编程密切关系到编译步骤 -- 解析、句法分析、转换和代码生成。

> Lean 4 是用 Lean 本身重新实现的 Lean 定理证明器。新的编译器生成 C 代码，用户现在可以在 Lean 中实现高效的证明自动化，将其编译为高效的 C 代码，并将其作为插件加载。在 Lean 4 中，用户只需导入 Lean 包即可访问用于实现 Lean 的所有内部数据结构。
>
> Leonardo de Moura、Sebastian Ullrich ([Lean 4 定理证明器和编程语言](https://pp.ipd.kit.edu/uploads/publikationen/demoura21lean4.pdf))

Lean 编译过程可以总结为下图：

<p align="center">
<img width="700px" src="https://github.com/arthurpaulino/lean4-metaprogramming-book/assets/7578559/78867009-2624-46a3-a1f4-f488fd25d494"/>
</p>

首先从字符串形式的 Lean 代码开始。然后它变成 `Syntax` 对象，然后是 `Expr` 对象。最后执行它。

因此，编译器看到一串 Lean 代码，例如 `"let a := 2"`，然后展开以下过程：

1. **应用相关句法规则** (`"let a := 2"` ➤ `Syntax`)

在解析步骤中，Lean 尝试将一串 Lean 代码与声明的**句法规则**之一进行匹配，以便将该字符串转换为 `Syntax` 对象。**句法规则**基本上是美化的正则表达式 -- 当您编写与某个**句法规则**的正则表达式匹配的 Lean 字符串时，该规则将用于处理后续步骤。

2. **循环应用所有宏** (`Syntax` ➤ `Syntax`)

在繁饰步骤中，每个**宏**只是将现有的 `Syntax` 对象转换为某个新的 `Syntax` 对象。然后，新的 `Syntax` 以类似的方式处理（重复步骤 1 和 2），直到没有更多**宏**可应用。

3. **应用单个 elab** (`Syntax` ➤ `Expr`)

最后，是时候为你的句法注入意义了 -- Lean 通过 `name` 参数找到与相应**句法规则**匹配的 **elab**（**句法规则**、**宏** 和 **elabs** 都有此参数，并且它们必须匹配）。新发现的 **elab** 返回特定的 `Expr` 对象。

这样就完成了繁饰步骤。​​

然后，表达式（`Expr`）在求值步骤中转换为可执行代码 -- 我们不必以任何方式指定，Lean 编译器将为我们处理此操作。

## 繁饰和反繁饰

繁饰（elaboration）是 Lean 中一个被重载的术语。例如，您可能会遇到以下用法，其意图是「采用部分指定的表达式并推断出剩下的隐含内容」：

> 当您输入一个表达式，如 `λ x y z, f (x + y) z` 供 Lean 处理时，您隐含了一些信息。例如，必须从上下文中推断出 `x`、`y` 和 `z` 的类型，符号 `+` 可能被重载，并且 `f` 可能有需要补全的隐参数。
>
> 「采用部分指定的表达式并推断出剩下的隐含内容」的过程称为**繁饰**。Lean 的**繁饰**算法功能强大，但同时又微妙而复杂。在依值类型论系统中工作需要知道**繁饰器**可以可靠地推断哪些类型的信息，以及知道如何响应繁饰器失败时引发的错误消息。为此，了解 Lean 的**繁饰器**如何工作会很有帮助。
>
> 当 Lean 解析表达式时，它首先进入预处理阶段。首先，Lean 为隐参数插入「洞」。如果项 t 的类型为 `Π {x : A}, P x`，则 t 在所有地方都将被 `@t _` 替换。然后，项中的洞（无论是在上一步中插入的洞还是用户明确编写的洞）由元变量 `?M1`、`?M2`、`?M3` 等实例化。每个重载符号都与一个选项列表相关联，即可能的解释。类似地，Lean 尝试检测在一个应用 `s t` 中可能需要插入强制转换的点，以使推断出的 t 类型与 `s` 的参数类型相匹配。这些也成为选择点。如果繁饰过程的一个可能结果是不需要强制转换，那么列表中的选择之一就是恒等式。
>
> ([Lean 2 中的定理证明](http://leanprover.github.io/tutorial/08_Building_Theories_and_Proofs.html))

另一方面，我们只是将繁饰定义为将 `Syntax` 对象转换为 `Expr` 对象的过程。

这些定义并不相互排斥。此处定义繁饰是将 `Syntax` 转换为 `Expr`，只是为了实现这种转换，我们需要很多技巧。我们需要推断隐式参数、实例化元变量、执行统一、解析标识符等。其他地方只是把这些繁饰操作的一部分也称为繁饰。

在 Lean 中，还存在一个与繁饰相反的反繁饰（delaboration）过程。在反繁饰过程中，一个 `Expr` 被转换成一个 `Syntax` 对象；然后格式化程序将其转换成一个 `Format` 对象，该对象可以在 Lean 的信息视图中显示。每次您将某些内容记录到屏幕上，或者将鼠标悬停在 `#check` 上时看到一些输出，这都是反繁饰器的工作。

本书中，您将看到对繁饰器的引用；在「附加内容：美观打印」一章中，您可以阅读有关反繁饰器的内容。

## 3个必要命令及其语法糖

现在，当你阅读 Lean 源代码时，你会看到 11 (或更多) 条命令指定**解析**/**繁饰**/**求值**过程：

<p align="center">
<img width="500px" src="https://github.com/arthurpaulino/lean4-metaprogramming-book/assets/7578559/9b83f06c-49c4-4d93-9d42-72e0499ae6c8"/>
</p>

在上图中，您可以看到 `notation`、`prefix`、`infix` 和 `postfix` -- 所有这些都是 `syntax` 和 `@[macro xxx] def ourMacro` 的组合，就像 `macro` 一样。这些命令与 `macro` 不同，因为您只能用它们定义特定形式的语法。

所有这些命令都在 Lean 和 Mathlib 源代码中广泛使用，最好记住。然而，它们中的大多数都是语法糖，您可以通过研究以下 3 个低级命令的行为来了解它们的行为：`syntax`（**句法规则**）、`@[macro xxx] def ourMacro`（**宏**）和 `@[command_elab xxx] def ourElab`（**elab**，繁饰 elaborate 的简写）。

举一个更具体的例子，假设我们正在实现一个 `#help` 命令，也可以写成 `#h`。然后我们可以按如下方式编写我们的**句法规则**、**宏**和**elab**：

<p align="center">
<img width="900px" src="https://github.com/lakesare/lean4-metaprogramming-book/assets/7578559/adc1284f-3c0a-441d-91b8-7d87b6035688"/>
</p>

这张图不是按行看的 -- 将 `macro_rules` 与 `elab` 一起使用是完全没问题的。但是，假设我们使用 3 个低级命令来指定我们的 `#help` 命令（第一行）。完成此操作后，我们可以编写 `#help "#explode"` 或 `#h "#explode"`，这两个命令都会输出 `#explode` 命令的相当简洁的文档 -- 「**Displays proof in a Fitch table**」。

如果我们编写 `#h "#explode"`，Lean 将遵循 `syntax (name := Shortcut_h)` ➤ `@[macro Shortcut_h] def helpMacro` ➤ `syntax (name := default_h)` ➤ `@[command_elab default_h] def helpElab` 路径。

如果我们写 `#help "#explode"`，Lean 将遵循 `syntax (name := default_h)` ➤ `@[command_elab default_h] def helpElab` 路径。

请注意，**句法规则**、**宏** 和 **elab** 之间的匹配是通过 `name` 参数完成的。如果我们使用 `macro_rules` 或其他语法糖，Lean 将自行找出适当的 `name` 参数。

如果我们定义的不是命令，我们可以写 `: term`、`: tactic` 或任何其他语法类别来替换 `: command`。
elab 函数也可以是不同的类型，例如用于实现 `#help` 的 `CommandElab` 还有 `TermElab` 和 `Tactic`:

- `TermElab` 代表 **Syntax → Option Expr → TermElabM Expr**，因此 elab 函数应该返回 **Expr** 对象。
- `CommandElab` 代表 **Syntax → CommandElabM Unit**，因此它不应该返回任何内容。
- `Tactic` 代表 **Syntax → TacticM Unit**，因此它不应该返回任何内容。

这对应于我们对 Lean 中的项、命令和策略的直观理解 -- 项在执行时返回特定值，命令修改环境或打印某些内容，策略修改证明状态。

## 执行顺序：句法规则、宏、elab

上面是这三个基本命令的执行流程，现在明确地阐述一下。执行顺序遵循以下伪代码模板：`syntax (macro; syntax)* elab`。

考虑以下示例。（我们将在后面的章节详细解释具体语法）
-/
import Lean
open Lean Elab Command

syntax (name := xxx) "red" : command
syntax (name := yyy) "green" : command
syntax (name := zzz) "blue" : command

@[macro xxx] def redMacro : Macro := λ stx =>
  match stx with
  | _ => `(green)

@[macro yyy] def greenMacro : Macro := λ stx =>
  match stx with
  | _ => `(blue)

@[command_elab zzz] def blueElab : CommandElab := λ stx =>
  Lean.logInfo "finally, blue!"

red -- 蓝色下划线输出：finally, blue!

/-
流程如下：

- 匹配适当的 `syntax` 规则（恰好有 `name := xxx`）➤
    应用 `@[macro xxx]` ➤

- 匹配适当的 `syntax` 规则（恰好有 `name := yyy`）➤
    应用 `@[macro yyy]` ➤

- 匹配适当的 `syntax` 规则（恰好有 `name := zzz`）➤
    找不到任何名称为 `zzz` 的宏来应用，
    因此应用 `@[command_elab zzz]`。🎉。

可以从这些基本原理中理解语法糖（`elab`、`macro` 等）的行为。

## `Syntax` / `Expr` / 可执行代码之间的手动转换

如果您使用 `syntax`、`macro` 和 `elab` 命令，Lean 将自动为您执行上述 **解析**/**繁饰**/**求值** 步骤，但是，当您编写策略时，您也经常需要手动执行这些转换。您可以使用以下函数来实现：

<p align="center">
<img width="650px" src="https://github.com/arthurpaulino/lean4-metaprogramming-book/assets/7578559/b403e650-dab4-4843-be8c-8fb812695a3a"/>
</p>

请注意，所有允许我们将 `Syntax` 转换为 `Expr` 的函数都以「elab」开头；所有允许我们将 `Expr`（或 `Syntax`）转换为 `actual code` 的函数都以「eval」（求值 evaluation 的简写）开头。

## 赋予含义：宏 VS 繁饰？

原则上，您可以使用 `macro` 执行（几乎？）任何可以使用 `elab` 函数执行的操作。只需将您在 `elab` 主体中的内容写成 `macro` 中的语法即可。但是，这里的经验法则是，仅当转换足够简单基本，几乎仅需重命名操作时才使用 `macro`。正如 Henrik Böving 所说：「一旦涉及类型或控制流，宏可能就不再合理了」（[出自Zulip](https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/The.20line.20between.20term.20elaboration.20and.20macro/near/280951290))。

因此，使用 `macro` 来创建语法糖、符号和快捷方式，并优先使用 `elab` 来编写带有一些编程逻辑的代码，即使它可能可以在 `macro` 中实现。

## 附加内容

### 打印消息

在 `#assertType` 示例中，我们使用 `logInfo` 来让我们的命令打印一些内容。如果我们只是想进行快速调试，我们可以使用 `dbg_trace`。

但它们的行为略有不同，如下所示：
-/

elab "traces" : tactic => do
  let array := List.replicate 2 (List.range 3)
  Lean.logInfo m!"logInfo: {array}"
  dbg_trace f!"dbg_trace: {array}"

example : True := by -- `example` 的蓝色下划线输出：dbg_trace: [[0, 1, 2], [0, 1, 2]]

  traces -- 现在 `traces` 的蓝色下划线输出：logInfo: [[0, 1, 2], [0, 1, 2]]

  trivial

/-
### 类型正确性

由于元层面中定义的对象不是我们最感兴趣的证明定理的对象，因此证明它们的类型正确有时可能过于繁琐。例如，我们不关心证明遍历表达式的递归函数是否合理。因此，如果我们确信函数终止，我们可以使用 `partial` 关键字。在最坏的情况下，我们的函数会陷入循环，导致 Lean 服务器在 VSCode 中崩溃，但内核中实现的底层类型论的合理性不受影响。
-/
