/-
#  Lean4 速查表

## 读取信息

* 读取目标：`Lean.Elab.Tactic.getMainGoal`

  用法：`let goal ← Lean.Elab.Tactic.getMainGoal`
* 读取元变量外声明：`mvarId.getDecl`
  当 `mvarId : Lean.MVarId` 在语境中
  例如，`mvarId` 可以是被 `getMainGoal` 读取到的目标。
* 读取元变量的类型：`mvarId.getType`
  当 `mvarId : Lean.MVarId` 在语境中
* 读取主目标的类型：`Lean.Elab.Tactic.getMainTarget`

  用法： `let goal_type ← Lean.Elab.Tactic.getMainTarget`

  等价实现：
```lean
let goal ← Lean.Elab.Tactic.getMainGoal
let goal_type ← goal.getType
```
* 读取局部语境：`Lean.MonadLCtx.getLCtx`

  用法：`let lctx ← Lean.MonadLCtx.getLCtx`
* 读取声明的名称：`Lean.LocalDecl.userName ldecl`
  当 `ldecl : Lean.LocalDecl` 在语境中
* 读取表达式的类型 `Lean.Meta.inferType expr`
  当 `expr : Lean.Expr` 是语境中的表达式

  用法：`let expr_type ← Lean.Meta.inferType expr`

##  操纵表达式

* 把声明转换为表达式：`Lean.LocalDecl.toExpr`

  用法：`ldecl.toExpr`，当 `ldecl : Lean.LocalDecl` 在语境中

  例如，`ldecl` 可以是 `let ldecl ← Lean.MonadLCtx.getLCtx`
* 检查两个表达式是否定义等价：`Lean.Meta.isDefEq ex1 ex2`
  当 `ex1 ex2 : Lean.Expr` 在语境中。返回一个 `Lean.MetaM Bool`
* 选择一个目标：`Lean.Elab.Tactic.closeMainGoal expr`
  当 `expr : Lean.Expr` 在语境中

## 更多命令

* meta-sorry: `Lean.Elab.admitGoal goal`，当 `goal : Lean.MVarId` 是当前目标

## 打印和显示报错

* 打印一句话：

  `Lean.logInfo f!"Hi, I will print\n{Syntax}"`
* 调试时打印：

  `dbg_trace f!"1) goal: {Syntax_that_will_be_interpreted}"`.
* 抛出错误信息：`Lean.Meta.throwTacticEx name mvar message_data`
  其中，`name : Lean.Name` 是策略名，`mvar` 包含错误信息

  用法：`Lean.Meta.throwTacticEx `tac goal (m!"unable to find matching hypothesis of type ({goal_type})")`
  其中，`m!` 格式化用于构建 `MessageData`，以便更好地打印项。

TODO: Add?
* Lean.LocalContext.forM
* Lean.LocalContext.findDeclM?
-/
