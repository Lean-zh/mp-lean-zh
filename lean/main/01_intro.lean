/-
# 介绍

## 本书的目的

本书的目的是教你 Lean 4 元编程，你将学会：

- 构建自己的元助手（定义新的 Lean 符号，如「∑」，构建新的 Lean 命令，如`#check`，编写策略，如`use`等）
- 阅读和讨论元编程API，如Lean 4 core和Mathlib4中的API

我们绝不打算对整个 Lean 4 元编程API进行详尽的解释。我们也不涉及单子（Monad）化编程的主题。我们希望示例足够简单，不太熟悉单子化编程也能跟上。强烈推荐[ Lean 中的函数式编程](https://www.leanprover.cn/fp-lean-zh/)作为这个主题的参考。

## 本书的结构

本书试着为DSL和策略建立足够的上下文来使你理解它们。章节依赖关系如下：

* 「策略」建立在「宏」和「繁饰」之上
* 「DSL」建立在「繁饰」之上
* 「宏」建立在「句法」之上
* 「繁饰」建立在「句法」和「MetaM」之上
* 「MetaM」建立在「表达式」之上

证明策略一章之后是包括关键概念和功能概述的备忘录。那之后，是一些章节额的外内容，展示了 Lean 4 元编程的其他应用。大多数章节的末尾都有习题，书的最后是习题答案。

本章的其余部分将简要介绍什么是元编程，并提供一些小示例开胃菜。

注意：代码片段不是自包含的。它们应该从每章的开头开始，以增量方式运行/读取。

## 「元」是什么?

当我们用Python、C、Java或Scala等大多数编程语言编写代码时，通常遵循预定义的句法，否则编译器或解释器将无法理解代码。在Lean中，这些预定义句法是定义归纳类型、实现函数、证明定理等。然后，编译器必须解析代码，构建一个AST（抽象句法树），并将其句法节点阐释为语言内核可以处理的项。我们说编译器执行的这些活动是在**元**层面中完成的，这是本书的内容。我们还说，句法的常见用法是在**对象**层面中完成的。

在大多数系统中，元层面活动是用与我们当前用来编写代码的语言不同的语言完成的。在Isabelle中，元层面语言是ML和Scala。在Coq中，它是OCaml。在Agda中，是Haskell。在 Lean 4 中，元代码主要是用 Lean 本身编写的，还有一些用C++编写的组件。

Lean 的一个很酷且方便的地方是，它允许我们用日常在对象层面写 Lean 的方式自定义句法节点，并实现元层面例程。例如，可以编写符号来实例化某种类型的项，并在同一个文件中立即使用它！这个概念通常被称为[**反射**](https://zh.wikipedia.org/wiki/%E5%8F%8D%E5%B0%84%E5%BC%8F%E7%BC%96%E7%A8%8B)。我们可以说，在Lean中，元层面被「反射」到对象层面。

用Ruby、Python或Javascript等语言做元编程的方式可能是使用预定义的元编程方法来即时定义一些东西。例如，在Ruby中你可以使用 `Class.new` 和 `define_method` 用于在程序执行时即时定义一个新类及其新方法（其中包含新代码！）。

在Lean中，我们通常不需要「即时地」定义新的命令或策略，但是在Lean元编程中能做类似的事，并且同样直接，例如，你可以使用简单的一行 `elab "#help" : command => do ...normal Lean code...`。

然而，在Lean中，我们经常想要直接操作Lean的CST（具体句法树，Lean的 `Syntax` 类型）和Lean的AST（抽象句法树，Lean的 `Expr` 类型），而不是使用「正常的Lean代码」，特别是当我们编写证明策略（Tactic）时。因此，Lean元编程更难掌握。本书的大部分内容都是为了研究这些类型以及我们如何操作它们。

## 元编程示例

下面这些例子仅作为展示。如果您现在不了解细节，请不要担心。

### 引入符号（定义新句法）

通常，人们希望引入新的符号，例如更适合数学（的某分支）的符号。例如，在数学中，人们会将给一个自然数加 `2` 的函数写为 `x : Nat ↦ x + 2` 或简单地写为 `x ↦ x + 2` ，如果可以推断出定义域是自然数。相应的 Lean 定义 `fun x : Nat => x + 2` 和 `fun x => x + 2` 使用 `=>`，这在数学中表示**蕴涵**，因此可能会让一些人感到困惑。
-/

import Lean

macro x:ident ":" t:term " ↦ " y:term : term => do
  `(fun $x : $t => $y)

#eval (x : Nat ↦ x + 2) 2 -- 4

macro x:ident " ↦ " y:term : term => do
  `(fun $x  => $y)

#eval (x ↦  x + 2) 2 -- 4

/-!

### 构建指令

构建一个辅助命令 `#assertType`，它宣布给定的项是否属于某种类型。用法如下：

`#assertType <term> : <type>`

代码是：
-/

elab "#assertType " termStx:term " : " typeStx:term : command =>
  open Lean Lean.Elab Command Term in
  liftTermElabM
    try
      let tp ← elabType typeStx
      discard $ elabTermEnsuringType termStx tp
      synthesizeSyntheticMVarsNoPostponing
      logInfo "success"
    catch | _ => throwError "failure"

/-- info: success -/
#guard_msgs in --#
#assertType 5  : Nat

/-- error: failure -/
#guard_msgs in --#
#assertType [] : Nat

/-!

`elab` 启动 `command` 句法的定义。当被编译器解析时，它将触发接下来的计算。

此时，代码应该在单子 `CommandElabM` 中运行。然后我们使用 `liftTermElabM` 来访问单子 `TermElabM`，这使我们能够使用 `elabType` 和 `elabTermEnsuringType` 从语法节点 `typeStx` 和 `termStx` 构建表达式。

首先，我们繁饰预期的类型 `tp : Expr`，然后使用它来繁饰项表达式。该项应具有类型 `tp`，否则将引发错误。然后我们丢弃生成的项表达式，因为它对我们来说并不重要 - 我们调用 `elabTermEnsuringType` 作为健全性检查。

我们还添加了 `synthesizeSyntheticMVarsNoPostponing`，它强制 Lean 立即繁饰元变量。如果没有该行，`#assertType [] : ?_` 将导致 `success`。

如果到现在为止没有抛出任何错误，则繁饰成功，我们可以使用 `logInfo` 输出 success 。相反，如果捕获到某些错误，则我们使用 `throwError` 并显示相应的消息。

We also add `synthesizeSyntheticMVarsNoPostponing`, which forces Lean to
elaborate metavariables right away. Without that line, `#assertType [] : ?_`
would result in `success`.

If no error is thrown until now then the elaboration succeeded and we can use
`logInfo` to output "success". If, instead, some error is caught, then we use
`throwError` with the appropriate message.

### Building a DSL and a syntax for it

Let's parse a classic grammar, the grammar of arithmetic expressions with
addition, multiplication, naturals, and variables.  We'll define an AST
(Abstract Syntax Tree) to encode the data of our expressions, and use operators
`+` and `*` to denote building an arithmetic AST. Here's the AST that we will be
parsing:
-/

inductive Arith : Type where
  | add : Arith → Arith → Arith -- e + f
  | mul : Arith → Arith → Arith -- e * f
  | nat : Nat → Arith           -- constant
  | var : String → Arith        -- variable

/-! Now we declare a syntax category to describe the grammar that we will be
parsing. Notice that we control the precedence of `+` and `*` by giving a lower
precedence weight to the `+` syntax than to the `*` syntax indicating that
multiplication binds tighter than addition (the higher the number, the tighter
the binding). This allows us to declare _precedence_ when defining new syntax.
-/

declare_syntax_cat arith
syntax num                        : arith -- nat for Arith.nat
syntax str                        : arith -- strings for Arith.var
syntax:50 arith:50 " + " arith:51 : arith -- Arith.add
syntax:60 arith:60 " * " arith:61 : arith -- Arith.mul
syntax " ( " arith " ) "          : arith -- bracketed expressions

-- Auxiliary notation for translating `arith` into `term`
syntax " ⟪ " arith " ⟫ " : term

-- Our macro rules perform the "obvious" translation:
macro_rules
  | `(⟪ $s:str ⟫)              => `(Arith.var $s)
  | `(⟪ $num:num ⟫)            => `(Arith.nat $num)
  | `(⟪ $x:arith + $y:arith ⟫) => `(Arith.add ⟪ $x ⟫ ⟪ $y ⟫)
  | `(⟪ $x:arith * $y:arith ⟫) => `(Arith.mul ⟪ $x ⟫ ⟪ $y ⟫)
  | `(⟪ ( $x ) ⟫)              => `( ⟪ $x ⟫ )

#check ⟪ "x" * "y" ⟫
-- Arith.mul (Arith.var "x") (Arith.var "y") : Arith

#check ⟪ "x" + "y" ⟫
-- Arith.add (Arith.var "x") (Arith.var "y") : Arith

#check ⟪ "x" + 20 ⟫
-- Arith.add (Arith.var "x") (Arith.nat 20) : Arith

#check ⟪ "x" + "y" * "z" ⟫ -- precedence
-- Arith.add (Arith.var "x") (Arith.mul (Arith.var "y") (Arith.var "z")) : Arith

#check ⟪ "x" * "y" + "z" ⟫ -- precedence
-- Arith.add (Arith.mul (Arith.var "x") (Arith.var "y")) (Arith.var "z") : Arith

#check ⟪ ("x" + "y") * "z" ⟫ -- brackets
-- Arith.mul (Arith.add (Arith.var "x") (Arith.var "y")) (Arith.var "z")

/-!
### Writing our own tactic

Let's create a tactic that adds a new hypothesis to the context with a given
name and postpones the need for its proof to the very end. It's similar to
the `suffices` tactic from Lean 3, except that we want to make sure that the new
goal goes to the bottom of the goal list.

It's going to be called `suppose` and is used like this:

`suppose <name> : <type>`

So let's see the code:
-/

open Lean Meta Elab Tactic Term in
elab "suppose " n:ident " : " t:term : tactic => do
  let n : Name := n.getId
  let mvarId ← getMainGoal
  mvarId.withContext do
    let t ← elabType t
    let p ← mkFreshExprMVar t MetavarKind.syntheticOpaque n
    let (_, mvarIdNew) ← MVarId.intro1P $ ← mvarId.assert n t p
    replaceMainGoal [p.mvarId!, mvarIdNew]
  evalTactic $ ← `(tactic|rotate_left)

example : 0 + a = a := by
  suppose add_comm : 0 + a = a + 0
  rw [add_comm]; rfl     -- closes the initial main goal
  rw [Nat.zero_add]; rfl -- proves `add_comm`

/-! We start by storing the main goal in `mvarId` and using it as a parameter of
`withMVarContext` to make sure that our elaborations will work with types that
depend on other variables in the context.

This time we're using `mkFreshExprMVar` to create a metavariable expression for
the proof of `t`, which we can introduce to the context using `intro1P` and
`assert`.

To require the proof of the new hypothesis as a goal, we call `replaceMainGoal`
passing a list with `p.mvarId!` in the head. And then we can use the
`rotate_left` tactic to move the recently added top goal to the bottom.

-/
