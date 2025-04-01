/-
# 证明策略
证明策略(Tactic)是 Lean 程序，用于操纵自定义状态。最终，所有策略都属于 `TacticM Unit` 类型。其类型为：

```lean
-- 来自 Lean/Elab/Tactic/Basic.lean
TacticM = ReaderT Context $ StateRefT State TermElabM
```

但在演示如何使用 `TacticM` 之前，我们将探索基于宏的策略。

## 通过宏扩展的策略

与 Lean 4 基础架构的许多其他部分一样，策略也可以通过轻量级宏扩展来声明。

例如下面的 `custom_sorry_macro` 示例，该示例繁饰为 `sorry`。我们将其写为宏扩展，将语法片段 `custom_sorry_macro` 扩展为语法片段 `sorry`：
-/

import Lean.Elab.Tactic

macro "custom_sorry_macro" : tactic => `(tactic| sorry)

example : 1 = 42 := by
  custom_sorry_macro

/-
### 实现 `trivial`：通过宏扩展实现可扩展的策略

作为更复杂的示例，我们可以编写一个类似 `custom_tactic` 的策略，该策略最初完全未实现，并且可以通过添加更多策略来扩展。我们首先简单地声明这个策略，而不提供任何实现：
-/

syntax "custom_tactic" : tactic
/-
```lean
/-- 错误：策略 'tacticCustom_tactic' 尚未实现 -/
#guard_msgs in --#
example : 42 = 42 := by
  custom_tactic
  sorry
```
-/
/-
接下来我们将在 `custom_tactic` 中添加 `rfl` 策略，这将允许我们证明前面的定理。
-/

macro_rules
| `(tactic| custom_tactic) => `(tactic| rfl)

example : 42 = 42 := by
   custom_tactic
-- Goals accomplished 🎉

/-
测试一个稍难的例子，它不能直接被 `rfl` 证明：
-/

#check_failure (by custom_tactic : 43 = 43 ∧ 42 = 42)
-- type mismatch
--   Iff.rfl
-- has type
--   ?m.1437 ↔ ?m.1437 : Prop
-- but is expected to have type
--   43 = 43 ∧ 42 = 42 : Prop

/-
我们通过一个策略扩展 `custom_tactic`，该策略尝试使用 `apply And.intro` 分解 `And`，然后递归地对两个子情况应用 `custom_tactic`，并使用 `(<;> trivial)` 解决生成的子问题 `43 = 43` 和 `42 = 42`。
-/

macro_rules
| `(tactic| custom_tactic) => `(tactic| apply And.intro <;> custom_tactic)

/-
上面的声明使用了 `<;>`，这是一种**策略组合器**（tactic combinator）。这里，`a <;> b` 的意思是「运行策略 `a`，并对 `a` 生成的每个目标应用 `b`」。因此，`And.intro <;> custom_tactic` 的意思是「运行 `And.intro`，然后在每个目标上运行 `custom_tactic`」。我们在前面的定理上测试它，并发现我们能够证明该定理。
-/

example : 43 = 43 ∧ 42 = 42 := by
  custom_tactic
-- Goals accomplished 🎉

/-
总结一下，我们声明了一个可扩展的策略，名为 `custom_tactic`。最初，它完全没有任何实现。我们将 `rfl` 作为 `custom_tactic` 的一个实现，这使它能够解决目标 `42 = 42`。然后我们尝试了一个更难的定理 `43 = 43 ∧ 42 = 42`，而 `custom_tactic` 无法解决。随后我们丰富了 `custom_tactic`，使其能够通过 `And.intro` 分解「AND」，并且在两个子情况下递归调用 `custom_tactic`。

### 实现 `<;>`：通过宏扩展实现策略组合器

在上一节中，我们提到 `a <;> b` 意味着「运行 `a`，然后对所有生成的目标运行 `b`」。实际上，`<;>` 本身是一个策略宏。在本节中，我们将实现 `a and_then b` 语法，它代表「运行 `a`，然后对所有目标运行 `b`」。
-/

-- 1. 我们声明语法 `and_then`
syntax tactic " and_then " tactic : tactic

-- 2. 我们编写扩展器，将策略扩展为运行 `a`，然后对 `a` 生成的所有目标运行 `b`。
macro_rules
| `(tactic| $a:tactic and_then $b:tactic) =>
    `(tactic| $a:tactic; all_goals $b:tactic)

-- 3. 我们测试这个策略。
theorem test_and_then: 1 = 1 ∧ 2 = 2 := by
  apply And.intro and_then rfl

#print test_and_then
-- theorem test_and_then : 1 = 1 ∧ 2 = 2 :=
-- { left := Eq.refl 1, right := Eq.refl 2 }

/-
## 探索 `TacticM`

### 最简单的策略：`sorry`

本节我们实现sorry：

```lean
example : 1 = 2 := by
  custom_sorry
```

从声明策略开始：
-/

elab "custom_sorry_0" : tactic => do
  return

example : 1 = 2 := by
  custom_sorry_0
-- unsolved goals: ⊢ 1 = 2
  sorry

/-
这定义了一个 Lean 的语法扩展，我们将这个语法片段命名为 `custom_sorry_0`，属于 `tactic` 语法类别。这告诉繁饰器，在繁饰 `tactic` 时，`custom_sorry_0` 语法片段必须按照我们在 `=>` 右侧编写的内容进行繁饰（也就是策略的实际实现）。

接下来，我们编写一个 `TacticM Unit` 类型的项，用 `sorryAx α` 填充目标，它可以生成一个类型为 `α` 的人工项。为此，我们首先使用 `Lean.Elab.Tactic.getMainGoal : Tactic MVarId` 获取目标，它返回一个表示为元变量的主目标。回顾类型即命题的原理，我们的目标类型必须是命题 `1 = 2`。我们通过打印 `goal` 的类型来验证这一点。

但首先，我们需要使用 `Lean.Elab.Tactic.withMainContext` 开始我们的策略，它在更新后的语境中计算 `TacticM`。
-/

elab "custom_sorry_1" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let goalDecl ← goal.getDecl
    let goalType := goalDecl.type
    dbg_trace f!"goal type: {goalType}"

example : 1 = 2 := by
  custom_sorry_1
-- goal type: Eq.{1} Nat (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
-- unsolved goals: ⊢ 1 = 2
  sorry

/-
为了 `sorry` 这个目标，我们可以用 `Lean.Elab.admitGoal`：
-/

elab "custom_sorry_2" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    Lean.Elab.admitGoal goal

theorem test_custom_sorry : 1 = 2 := by
  custom_sorry_2

#print test_custom_sorry
-- theorem test_custom_sorry : 1 = 2 :=
-- sorryAx (1 = 2) true

/-
我们不再出现错误 `unsolved goals: ⊢ 1 = 2`。

### `custom_assump` 策略：访问假设

在本节中，我们将学习如何访问假设来证明目标。特别是，我们将尝试实现一个策略 `custom_assump`，它会在假设中寻找与目标完全匹配的项，并在可能的情况下解决定理。

在下面的例子中，我们期望 `custom_assump` 使用 `(H2 : 2 = 2)` 来解决目标 `(2 = 2)`：

```lean
theorem assump_correct (H1 : 1 = 1) (H2 : 2 = 2) : 2 = 2 := by
  custom_assump

#print assump_correct
-- theorem assump_correct : 1 = 1 → 2 = 2 → 2 = 2 :=
-- fun H1 H2 => H2
```

当我们没有与目标匹配的假设时，我们期望 `custom_assump` 策略抛出一个错误，告知我们找不到我们正在寻找类型的假设：

```lean
theorem assump_wrong (H1 : 1 = 1) : 2 = 2 := by
  custom_assump

#print assump_wrong
-- 策略 'custom_assump' 失败，找不到类型 (2 = 2) 的匹配假设
-- tactic 'custom_assump' failed, unable to find matching hypothesis of type (2 = 2)
-- H1 : 1 = 1
-- ⊢ 2 = 2
```

我们首先通过访问目标及其类型，来了解我们正在试图证明什么。`goal` 变量很快将被用于帮助我们创建错误信息。
-/

elab "custom_assump_0" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goalType ← Lean.Elab.Tactic.getMainTarget
    dbg_trace f!"goal type: {goalType}"

example (H1 : 1 = 1) (H2 : 2 = 2): 2 = 2 := by
  custom_assump_0
-- goal type: Eq.{1} Nat (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
-- unsolved goals
-- H1 : 1 = 1
-- H2 : 2 = 2
-- ⊢ 2 = 2
  sorry

example (H1 : 1 = 1): 2 = 2 := by
  custom_assump_0
-- goal type: Eq.{1} Nat (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
-- unsolved goals
-- H1 : 1 = 1
-- ⊢ 2 = 2
  sorry

/-
接下来，我们访问存储在名为 `LocalContext` 的数据结构中的假设列表。可以通过 `Lean.MonadLCtx.getLCtx` 访问它。`LocalContext` 包含 `LocalDeclaration`，我们可以从中提取信息，如声明的名称（`.userName`）和声明的表达式（`.toExpr`）。让我们编写一个名为 `list_local_decls` 的策略，打印出局部声明：
-/

elab "list_local_decls_1" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let ctx ← Lean.MonadLCtx.getLCtx -- 获取局部语境
    ctx.forM fun decl: Lean.LocalDecl => do
      let declExpr := decl.toExpr -- 找到声明的表达式
      let declName := decl.userName -- 找到声明的名称
      dbg_trace f!"+ local decl: name: {declName} | expr: {declExpr}"

example (H1 : 1 = 1) (H2 : 2 = 2): 1 = 1 := by
  list_local_decls_1
-- + local decl: name: test_list_local_decls_1 | expr: _uniq.3339
-- + local decl: name: H1 | expr: _uniq.3340
-- + local decl: name: H2 | expr: _uniq.3341
  rfl

/-
回想一下，我们正在寻找一个具有与假设相同类型的局部声明。我们可以通过在局部声明的表达式上调用 `Lean.Meta.inferType` 来获取 `LocalDecl` 的类型。
-/

elab "list_local_decls_2" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let ctx ← Lean.MonadLCtx.getLCtx -- 获取局部语境
    ctx.forM fun decl: Lean.LocalDecl => do
      let declExpr := decl.toExpr -- 找到声明的表达式
      let declName := decl.userName -- 找到声明的名称
      let declType ← Lean.Meta.inferType declExpr -- **新事件：** 找到类型
      dbg_trace f!"+ local decl: name: {declName} | expr: {declExpr} | type: {declType}"

example (H1 : 1 = 1) (H2 : 2 = 2): 1 = 1 := by
  list_local_decls_2
  -- + local decl: name: test_list_local_decls_2 | expr: _uniq.4263 | type: (Eq.{1} Nat ...)
  -- + local decl: name: H1 | expr: _uniq.4264 | type: Eq.{1} Nat ...)
  -- + local decl: name: H2 | expr: _uniq.4265 | type: Eq.{1} Nat ...)
  rfl

/-
我们使用 `Lean.Meta.isExprDefEq` 检查 `LocalDecl` 的类型是否与目标类型相等。可以看到，我们在 `eq?` 处检查类型是否相等，并打印出 `H1` 与目标类型相同（`local decl[EQUAL? true]: name: H1`），同时我们也打印出 `H2` 的类型不相同（`local decl[EQUAL? false]: name: H2`）：
-/

elab "list_local_decls_3" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goalType ← Lean.Elab.Tactic.getMainTarget
    let ctx ← Lean.MonadLCtx.getLCtx -- 获取局部语境
    ctx.forM fun decl: Lean.LocalDecl => do
      let declExpr := decl.toExpr -- 找到声明的表达式
      let declName := decl.userName -- 找到声明的名称
      let declType ← Lean.Meta.inferType declExpr -- 找到类型
      let eq? ← Lean.Meta.isExprDefEq declType goalType -- **新事件：** 检查是否与目标类型等价
      dbg_trace f!"+ local decl[EQUAL? {eq?}]: name: {declName}"

example (H1 : 1 = 1) (H2 : 2 = 2): 1 = 1 := by
  list_local_decls_3
-- + local decl[EQUAL? false]: name: test_list_local_decls_3
-- + local decl[EQUAL? true]: name: H1
-- + local decl[EQUAL? false]: name: H2
  rfl

/-
最后，我们将这些部分组合在一起，编写一个遍历所有声明并找到具有正确类型的声明的策略。我们使用 `lctx.findDeclM?` 遍历声明。使用 `Lean.Meta.inferType` 推断声明的类型。使用 `Lean.Meta.isExprDefEq` 检查声明的类型是否与目标相同：
-/

elab "custom_assump_1" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goalType ← Lean.Elab.Tactic.getMainTarget
    let lctx ← Lean.MonadLCtx.getLCtx
    -- 在局部证明中迭代...
    let option_matching_expr ← lctx.findDeclM? fun ldecl: Lean.LocalDecl => do
      let declExpr := ldecl.toExpr -- 找到声明的表达式
      let declType ← Lean.Meta.inferType declExpr -- 找到类型
      if (← Lean.Meta.isExprDefEq declType goalType) -- 检查是否与目标类型等价
      then return some declExpr -- 如果等价，成功！
      else return none          -- 未找到
    dbg_trace f!"matching_expr: {option_matching_expr}"

example (H1 : 1 = 1) (H2 : 2 = 2) : 2 = 2 := by
  custom_assump_1
-- matching_expr: some _uniq.6241
  rfl

example (H1 : 1 = 1) : 2 = 2 := by
  custom_assump_1
-- matching_expr: none
  rfl

/-
现在我们能够找到匹配的表达式，需要使用匹配来证成定理。我们通过 `Lean.Elab.Tactic.closeMainGoal` 来完成这一操作。如果没有找到匹配的表达式，我们会使用 `Lean.Meta.throwTacticEx` 抛出一个错误，允许我们针对给定的目标报告错误。在抛出此错误时，我们使用 `m!"..."` 来格式化错误信息，这会生成一个 `MessageData`。与生成 `Format` 的 `f!"..."` 相比，`MessageData` 提供了更友好的错误信息，这是因为 `MessageData` 还会运行**反繁饰**，使其能够将像 `(Eq.{1} Nat (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))` 这样的原始 Lean 项转换为易读的字符串，例如 `(2 = 2)`。完整的代码示例如下：
-/

elab "custom_assump_2" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let goalType ← Lean.Elab.Tactic.getMainTarget
    let ctx ← Lean.MonadLCtx.getLCtx
    let option_matching_expr ← ctx.findDeclM? fun decl: Lean.LocalDecl => do
      let declExpr := decl.toExpr
      let declType ← Lean.Meta.inferType declExpr
      if ← Lean.Meta.isExprDefEq declType goalType
        then return Option.some declExpr
        else return Option.none
    match option_matching_expr with
    | some e => Lean.Elab.Tactic.closeMainGoal `custom_assump_2 e
    | none =>
      Lean.Meta.throwTacticEx `custom_assump_2 goal
        (m!"unable to find matching hypothesis of type ({goalType})")

example (H1 : 1 = 1) (H2 : 2 = 2) : 2 = 2 := by
  custom_assump_2

#check_failure (by custom_assump_2 : (H1 : 1 = 1) → 2 = 2)
-- tactic 'custom_assump_2' failed, unable to find matching hypothesis of type (2 = 2)
-- H1 : 1 = 1
-- ⊢ 2 = 2

/-
### 调整语境

到目前为止，我们只对语境执行了类似读取的操作。但如果我们想要更改语境呢？在本节中，我们将看到如何更改目标的顺序以及如何向其添加内容（新的假设）。

然后，在繁饰我们的项之后，我们需要使用辅助函数 `Lean.Elab.Tactic.liftMetaTactic`，它允许我们在 `MetaM` 中运行计算，同时为我们提供目标 `MVarId` 以便操作。计算结束时，`liftMetaTactic` 期望我们返回一个 `List MVarId`，即目标列表的最终结果。

`custom_let` 和 `custom_have` 的唯一实质性区别是前者使用了 `Lean.MVarId.define`，而后者使用了 `Lean.MVarId.assert`：
-/

open Lean.Elab.Tactic in
elab "custom_let " n:ident " : " t:term " := " v:term : tactic =>
  withMainContext do
    let t ← elabTerm t none
    let v ← elabTermEnsuringType v t
    liftMetaTactic fun mvarId => do
      let mvarIdNew ← mvarId.define n.getId t v
      let (_, mvarIdNew) ← mvarIdNew.intro1P
      return [mvarIdNew]

open Lean.Elab.Tactic in
elab "custom_have " n:ident " : " t:term " := " v:term : tactic =>
  withMainContext do
    let t ← elabTerm t none
    let v ← elabTermEnsuringType v t
    liftMetaTactic fun mvarId => do
      let mvarIdNew ← mvarId.assert n.getId t v
      let (_, mvarIdNew) ← mvarIdNew.intro1P
      return [mvarIdNew]

theorem test_faq_have : True := by
  custom_let n : Nat := 5
  custom_have h : n = n := rfl
-- n : Nat := 5
-- h : n = n
-- ⊢ True
  trivial

/-
### 「获取」和「设置」目标列表

为了说明这些操作，我们将构建一个可以反转目标列表的策略。我们可以使用 `Lean.Elab.Tactic.getGoals` 和 `Lean.Elab.Tactic.setGoals`：
-/

elab "reverse_goals" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goals : List Lean.MVarId ← Lean.Elab.Tactic.getGoals
    Lean.Elab.Tactic.setGoals goals.reverse

theorem test_reverse_goals : (1 = 2 ∧ 3 = 4) ∧ 5 = 6 := by
  constructor
  constructor
-- case left.left
-- ⊢ 1 = 2
-- case left.right
-- ⊢ 3 = 4
-- case right
-- ⊢ 5 = 6
  reverse_goals
-- case right
-- ⊢ 5 = 6
-- case left.right
-- ⊢ 3 = 4
-- case left.left
-- ⊢ 1 = 2
  all_goals sorry

/-
## 常见问题

在本节中，我们收集了一些在编写策略时常用的模式，备查。

**问题：如何使用目标？**

回答：目标表示为元变量。模块 `Lean.Elab.Tactic.Basic` 提供了许多函数用于添加新目标、切换目标等。

**问题：如何获取主要目标？**

回答：使用 `Lean.Elab.Tactic.getMainGoal`。
-/

elab "faq_main_goal" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    dbg_trace f!"goal: {goal.name}"

example : 1 = 1 := by
  faq_main_goal
-- goal: _uniq.9298
  rfl

/-
**问题：如何获取目标列表？**

回答：使用 `getGoals`。
-/

elab "faq_get_goals" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goals ← Lean.Elab.Tactic.getGoals
    goals.forM $ fun goal => do
      let goalType ← goal.getType
      dbg_trace f!"goal: {goal.name} | type: {goalType}"

example (b : Bool) : b = true := by
  cases b
  faq_get_goals
-- goal: _uniq.10067 | type: Eq.{1} Bool Bool.false Bool.true
-- goal: _uniq.10078 | type: Eq.{1} Bool Bool.true Bool.true
  sorry
  rfl

/-
**问题：如何获取目标的当前假设？**

回答：使用 `Lean.MonadLCtx.getLCtx` 获取局部语境，然后使用诸如 `foldlM` 和 `forM` 之类的访问器，遍历 `LocalContext` 中的 `LocalDeclaration`。
-/

elab "faq_get_hypotheses" : tactic =>
  Lean.Elab.Tactic.withMainContext do
  let ctx ← Lean.MonadLCtx.getLCtx -- 获取局部语境。
  ctx.forM (fun (decl : Lean.LocalDecl) => do
    let declExpr := decl.toExpr -- 找到声明的表达式。
    let declType := decl.type -- 找到声明的类型。
    let declName := decl.userName -- 找到声明的名称。
    dbg_trace f!"局部声明: 名称: {declName} | 表达式: {declExpr} | 类型: {declType}"
  )

example (H1 : 1 = 1) (H2 : 2 = 2): 3 = 3 := by
  faq_get_hypotheses
  -- local decl: name: _example | expr: _uniq.10814 | type: ...
  -- local decl: name: H1 | expr: _uniq.10815 | type: ...
  -- local decl: name: H2 | expr: _uniq.10816 | type: ...
  rfl

/-
**问题：如何执行一个策略？**

回答：使用 `Lean.Elab.Tactic.evalTactic: Syntax → TacticM Unit` 来执行给定的策略语法。可以使用宏 `` `(tactic| ⋯)`` 创建策略语法。

例如，可以使用以下代码调用 `try rfl`：

```lean
Lean.Elab.Tactic.evalTactic (← `(tactic| try rfl))
```

**问题：如何检查两个表达式是否相等？**

回答：使用 `Lean.Meta.isExprDefEq <expr-1> <expr-2>`。
-/

#check Lean.Meta.isExprDefEq
-- Lean.Meta.isExprDefEq : Lean.Expr → Lean.Expr → Lean.MetaM Bool

/-
**问题：如何从一个策略中抛出错误？**

回答：使用 `throwTacticEx <tactic-name> <goal-mvar> <error>`。
-/

elab "faq_throw_error" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    Lean.Meta.throwTacticEx `faq_throw_error goal "throwing an error at the current goal"

#check_failure (by faq_throw_error : (b : Bool) → b = true)
-- tactic 'faq_throw_error' failed, throwing an error at the current goal
-- ⊢ ∀ (b : Bool), b = true

/-!
**问题：`Lean.Elab.Tactic.*` 和 `Lean.Meta.Tactic.*` 有什么区别？**

回答：`Lean.Meta.Tactic.*` 包含使用 `Meta` 单子实现的底层代码，用于提供诸如重写等基本功能。而 `Lean.Elab.Tactic.*` 包含连接 `Lean.Meta` 中的底层开发与策略基础设施及解析前端的高级代码。

## 练习

1. 考虑定理 `p ∧ q ↔ q ∧ p`。我们可以将其证明写为一个证明项，或者使用策略构建它。
   当我们将该定理的证明写成证明项时，我们会逐步用特定的表达式填充 `_`，一步一步进行。每一步都对应一个策略。

   我们可以通过多种步骤组合来编写这个证明项，但请考虑我们在下面编写的步骤序列。请将每一步写为策略。
   策略 `step_1` 已经填写，请对其余策略执行相同操作（为了练习，请尝试使用较底层的 API，例如 `mkFreshExprMVar`、`mvarId.assign` 和 `modify fun _ => { goals := ~)`）。

   ```lean
   -- [这是初始目标]
   example : p ∧ q ↔ q ∧ p :=
     _

   -- step_1
   example : p ∧ q ↔ q ∧ p :=
     Iff.intro _ _

   -- step_2
   example : p ∧ q ↔ q ∧ p :=
     Iff.intro
       (
         fun hA =>
         _
       )
       (
         fun hB =>
         (And.intro hB.right hB.left)
       )

   -- step_3
   example : p ∧ q ↔ q ∧ p :=
     Iff.intro
       (
         fun hA =>
         (And.intro _ _)
       )
       (
         fun hB =>
         (And.intro hB.right hB.left)
       )

   -- step_4
   example : p ∧ q ↔ q ∧ p :=
     Iff.intro
       (
         fun hA =>
         (And.intro hA.right hA.left)
       )
       (
         fun hB =>
         (And.intro hB.right hB.left)
       )
   ```

   ```lean
   elab "step_1" : tactic => do
     let mvarId ← getMainGoal
     let goalType ← getMainTarget

     let Expr.app (Expr.app (Expr.const `Iff _) a) b := goalType | throwError "Goal type is not of the form `a ↔ b`"

     -- 1. 创建具有适当类型的新 `_`。
     let mvarId1 ← mkFreshExprMVar (Expr.forallE `xxx a b .default) (userName := "red")
     let mvarId2 ← mkFreshExprMVar (Expr.forallE `yyy b a .default) (userName := "blue")

     -- 2. 将主目标分配给表达式 `Iff.intro _ _`。
     mvarId.assign (mkAppN (Expr.const `Iff.intro []) #[a, b, mvarId1, mvarId2])

     -- 3. 将新的 `_` 报告给 Lean，作为新的目标。
     modify fun _ => { goals := [mvarId1.mvarId!, mvarId2.mvarId!] }
   ```

   ```lean
   theorem gradual (p q : Prop) : p ∧ q ↔ q ∧ p := by
     step_1
     step_2
     step_3
     step_4
   ```

以下是这段内容的翻译：

---

2. 在第一个练习中，我们使用了较底层的 `modify` API 来更新我们的目标。`liftMetaTactic`、`setGoals`、`appendGoals`、`replaceMainGoal`、`closeMainGoal` 等都是在 `modify fun s : State => { s with goals := myMvarIds }` 之上的语法糖。请使用以下方法重写 `forker` 策略：

  **a)** `liftMetaTactic`
  **b)** `setGoals`
  **c)** `replaceMainGoal`

  ```lean
  elab "forker" : tactic => do
    let mvarId ← getMainGoal
    let goalType ← getMainTarget

    let (Expr.app (Expr.app (Expr.const `And _) p) q) := goalType | Lean.Meta.throwTacticEx `forker mvarId (m!"Goal is not of the form P ∧ Q")

    mvarId.withContext do
      let mvarIdP ← mkFreshExprMVar p (userName := "red")
      let mvarIdQ ← mkFreshExprMVar q (userName := "blue")

      let proofTerm := mkAppN (Expr.const `And.intro []) #[p, q, mvarIdP, mvarIdQ]
      mvarId.assign proofTerm

      modify fun state => { goals := [mvarIdP.mvarId!, mvarIdQ.mvarId!] ++ state.goals.drop 1 }
  ```

  ```lean
  example (A B C : Prop) : A → B → C → (A ∧ B) ∧ C := by
    intro hA hB hC
    forker
    forker
    assumption
    assumption
    assumption
  ```

3. 在第一个练习中，你在 `step_2` 中创建了自己的 `intro`（假设名是硬编码的，但基本原理是相同的）。在编写策略时，我们通常会使用 `intro`、`intro1`、`intro1P`、`introN` 或 `introNP` 等函数。

  对于下面的每一点，请创建一个名为 `introductor` 的策略（每一点对应一个策略），将目标 `(ab: a = b) → (bc: b = c) → (a = c)` 变为：

  **a)** 包含假设 `(ab✝: a = b)` 和 `(bc✝: b = c)` 的目标 `(a = c)`。
  **b)** 包含假设 `(ab: a = b)` 的目标 `(bc: b = c) → (a = c)`。
  **c)** 包含假设 `(hello: a = b)` 的目标 `(bc: b = c) → (a = c)`。

  ```lean
  example (a b c : Nat) : (ab: a = b) → (bc: b = c) → (a = c) := by
    introductor
    sorry
  ```

提示：`intro1P` 和 `introNP` 中的 "P" 代表 **"Preserve"**（保留）。
-/
